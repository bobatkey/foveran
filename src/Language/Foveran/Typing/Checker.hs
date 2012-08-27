{-# LANGUAGE OverloadedStrings, TypeOperators, DoAndIfThenElse #-}

module Language.Foveran.Typing.Checker
    ( TypingMonad ()
    , runTypingMonad
    , isType
    , synthesiseTypeFor
    , hasType )
    where

import           Control.Applicative (pure, (<*>), (<$>))
import           Control.Monad (unless)
import           Control.Monad.Trans (lift)
import           Control.Monad.Reader (ReaderT, runReaderT, ask, local)
import           Control.Monad.State (StateT, runStateT, get, modify)
import           Data.Maybe (fromMaybe)
import           Data.Rec (AnnotRec (Annot), Rec (In), annot)
import qualified Data.Map as M -- for doing the clauses in CasesOn
import           Text.Position (Span)
import           Language.Foveran.Syntax.Identifier (Ident, UsesIdentifiers (..), freshFor, (<+>))
import           Language.Foveran.Syntax.LocallyNameless (TermPos, TermCon (..), close, GlobalFlag (..), Binding (..), bindingOfPattern)
import           Language.Foveran.Syntax.Display (Pattern (..))
import qualified Language.Foveran.Syntax.Checked as CS
import           Language.Foveran.Typing.LocalContext
import           Language.Foveran.Typing.DefinitionContext
import           Language.Foveran.Typing.Hole
import           Language.Foveran.Typing.Conversion
import           Language.Foveran.Typing.Errors (TypeError (..))

{------------------------------------------------------------------------------}
type TypingMonad ctxt a
    = ReaderT ctxt (StateT Holes (ReaderT LocalContext (Either (Span, Holes, LocalContext, TypeError)))) a

getLocalContext :: TypingMonad ctxt LocalContext
getLocalContext = lift ask

getCurrentHoles :: TypingMonad ctxt Holes
getCurrentHoles = get

getFullContext :: TypingMonad ctxt (ctxt :>: LocalContext)
getFullContext = (:>:) <$> ask <*> getLocalContext

-- | Binds a variable in the local context, and invokes another typing
-- action in the extended context.
bindVar' :: UsesIdentifiers ctxt =>
            Int -- ^ Offset
         -> Ident -- ^ Name hint
         -> Value -- ^ The type of the newly bound identifier
         -> TermPos -- ^ Term to pass through, should have at least one free local variable
         -> (Value -> TermPos -> TypingMonad ctxt CS.Term)
         -> TypingMonad ctxt CS.Term
bindVar' offset nameHint typ tm k = do
  freshIdentifier <- freshFor <$> getFullContext <*> pure nameHint
  let tm' = close [freshIdentifier] tm offset
      v   = reflect typ (CS.tmFree freshIdentifier)
  context <- ask
  a <- lift $ local (extendWith freshIdentifier typ) (runReaderT (k v tm') context)
  return (CS.bindFree [freshIdentifier] a offset)

bindVar :: UsesIdentifiers ctxt =>
           Ident -- ^ Name hint
        -> Value -- ^ The type of the newly bound identifier
        -> TermPos -- ^ Term to pass through, should have at least one free local variable
        -> (Value -> TermPos -> TypingMonad ctxt CS.Term)
        -> TypingMonad ctxt CS.Term
bindVar = bindVar' 0

evalWith :: DefinitionContext ctxt =>
            CS.Term
         -> [Value]
         -> TypingMonad ctxt Value
evalWith term arguments =
    evalInWith <$> pure term <*> getFullContext <*> getCurrentHoles <*> pure arguments

evalA :: DefinitionContext ctxt =>
         CS.Term
      -> TypingMonad ctxt ([Value] -> Value)
evalA term =
    evalInWith <$> pure term <*> getFullContext <*> getCurrentHoles

eval :: DefinitionContext ctxt =>
        CS.Term
     -> TypingMonad ctxt Value
eval term =
    term `evalWith` []

lookupIdent :: DefinitionContext ctxt =>
               Ident
            -> GlobalFlag
            -> TypingMonad ctxt (Maybe Value)
lookupIdent ident IsGlobal =
    lookupType ident <$> ask -- "getGlobalContext"
lookupIdent ident IsLocal =
    lookupType ident <$> getLocalContext

raiseError :: Span -> TypeError -> TypingMonad ctxt a
raiseError p err = do
  typingContext <- getLocalContext
  holeContext   <- getCurrentHoles
  lift $ lift $ lift $ Left (p, holeContext, typingContext, err)

generateHole :: DefinitionContext context =>
                Span -> Maybe Ident -> Maybe Value -> TypingMonad context CS.Term
generateHole p nameHint holeType = do
  holeIdentifier <- freshFor <$> getCurrentHoles <*> pure (fromMaybe "hole" nameHint)
  localContext   <- getLocalContext
  let hole      = makeHole localContext holeType
      arguments = map (\(ident,_) -> In $ CS.Free ident) (localContextMembers localContext)
  modify $ extendWithHole holeIdentifier hole
  return $ (In $ CS.Hole holeIdentifier arguments)

runTypingMonad :: TypingMonad ctxt a
               -> ctxt
               -> Holes
               -> LocalContext
               -> Either (Span, Holes, LocalContext, TypeError) (a,Holes)
runTypingMonad c context holeContext localContext =
    runReaderT (runStateT (runReaderT c context) holeContext) localContext

--------------------------------------------------------------------------------
makeTag :: Value
        -> Value
        -> Value
        -> Ident
        -> Span
        -> TypingMonad ctxt TermPos
makeTag vI vD vi nm p = do
  let findTag [] = raiseError p (OtherError "Datatype has no constructors")
      findTag [(ident,_)]
          | ident == nm = return (Annot p $ UnitI)
          | otherwise   = raiseError p (OtherError "constructor not found")
      findTag ((ident,_):constrs)
          | ident == nm = return (Annot p $ Inl $ Annot p $ UnitI)
          | otherwise   = do t <- findTag constrs
                             return (Annot p $ Inr t)
  constrs <- getDatatypeInfo vI vD vi p
  findTag constrs

type DatatypeInfo = [(Ident, [Bool])]

getDatatypeInfo :: Value
                -> Value
                -> Value
                -> Span
                -> TypingMonad ctxt DatatypeInfo
getDatatypeInfo vI vD vi p = do
  (constrsDesc, argsDesc) <-
      case vD $$ vi of
        VIDesc_Sg constrsDesc argsDesc ->
            return (constrsDesc,argsDesc)
        _ ->
            raiseError p (OtherError "Not a datatype in canonical form")

  -- FIXME: going to have to do this on the reified normal form, so
  -- that we can look under the lambda. Otherwise, we'll have to just
  -- simulate what reify does. Interestingly, using 'undefined' will
  -- usually work, because the standard 'data' declarations never
  -- produce descriptions that switch on the value of sigmas after the
  -- first one
  let analyseDesc (VIDesc_Pair _ rest) =
          (True:)  <$> analyseDesc rest
      analyseDesc (VIDesc_Sg _ f) =
          (False:) <$> analyseDesc (f $$ undefined {- FIXME -})
      analyseDesc (VIDesc_K (VEq _ _ _ _)) =
          return []
      analyseDesc _ =
          raiseError p (OtherError "Datatype not in canonical form")

  let extractConstructors VEmpty _ = 
          do return []
      extractConstructors (VUnit (Just tag)) k =
          do args <- analyseDesc (argsDesc $$ k VUnitI)
             return [(tag, args)]
      extractConstructors (VSum (VUnit (Just tag)) rest) k =
          do here  <- analyseDesc (argsDesc $$ k (VInl VUnitI))
             there <- extractConstructors rest (k . VInr)
             return ((tag,here):there)
      extractConstructors _ _ =
          raiseError p (OtherError "Datatype not in canonical form")

  extractConstructors constrsDesc id

-- FIXME: do this in LocallyNameless
makeConstructorArguments :: Span -> [TermPos] -> TermPos
makeConstructorArguments p []     = Annot p $ Refl
makeConstructorArguments p (t:ts) = Annot p $ Pair t (makeConstructorArguments p ts)


{------------------------------------------------------------------------------}
compareTypes :: Span -> Value -> Value -> TypingMonad ctxt ()
compareTypes p v1 v2 =
    do let tm1 = reifyType0 v1
           tm2 = reifyType0 v2
       unless (CS.cmp (<=) tm2 tm1) $ do raiseError p (TypesNotEqual v1 v2)

{------------------------------------------------------------------------------}
-- | Check that something is a type
isType :: (UsesIdentifiers ctxt, DefinitionContext ctxt) =>
          TermPos
       -> TypingMonad ctxt CS.Term
isType (Annot p (Set l)) = do
  return (In $ CS.Set l)
isType (Annot p (Pi ident tA tB)) = do
  tmA  <- isType tA
  vtmA <- eval tmA
  tmB  <- bindVar (fromMaybe "__x" ident) vtmA tB $ \_ tB -> isType tB
  return (In $ CS.Pi (CS.Irrelevant ident) tmA tmB)
isType (Annot p (Sigma ident tA tB)) = do
  tmA  <- isType tA
  vtmA <- eval tmA
  tmB  <- bindVar (fromMaybe "__x" ident) vtmA tB $ \_ tB -> isType tB
  return (In $ CS.Sigma (CS.Irrelevant ident) tmA tmB)
isType (Annot p (Sum t1 t2)) = do
  tm1 <- isType t1
  tm2 <- isType t2
  return (In $ CS.Sum tm1 tm2)
isType (Annot p (Unit tag)) = do
  return (In $ CS.Unit (CS.Irrelevant tag))
isType (Annot p Empty) =do
  return (In $ CS.Empty)
isType (Annot p (Eq tA tB)) = do
  (tyA, tmA) <- synthesiseTypeFor tA
  (tyB, tmB) <- synthesiseTypeFor tB
  let tyA' = reifyType0 tyA
      tyB' = reifyType0 tyB
  -- FIXME: need to be able to do equality types for terms that aren't
  -- of synthesisable type.
  return (In $ CS.Eq tyA' tyB' tmA tmB)
isType (Annot p (SemI tD x tA)) = do
  (tyD, tmD) <- synthesiseTypeFor tD
  case tyD of
    VIDesc tyI -> do
      tmA <- bindVar x tyI tA $ \x tA -> isType tA
      let tmI = reifyType0 tyI
      return (In $ CS.SemI tmI tmD (CS.Irrelevant x) tmA)
    v ->
      raiseError (annot tD) (ExpectingIDesc v)
isType (Annot p (LiftI tD x tA i a tP tx)) = do
  (tyD, tmD) <- synthesiseTypeFor tD
  case tyD of
    VIDesc vI -> do
      tmA <- bindVar x vI tA $ \x tA -> isType tA
      vA  <- evalA tmA
      tmP <- bindVar' 1 i vI tP $ \vi tP -> do
               bindVar a (vA [vi]) tP $ \va tP -> do
                 isType tP
      vD <- eval tmD
      tmx <- tx `hasType` (vsemI vI vD x (\v -> vA [v]))
      let tmI = reifyType0 vI
      return (In $ CS.LiftI tmI tmD (CS.Irrelevant x) tmA (CS.Irrelevant i) (CS.Irrelevant a) tmP tmx)
    v -> do
      raiseError (annot tD) (ExpectingIDesc v)
isType (Annot p (Group nm ab Nothing)) = do
  return (In $ CS.Group nm ab Nothing)
isType (Annot p UserHole) = do
  generateHole p Nothing Nothing
isType term@(Annot p _) = do
  (ty,tm) <- synthesiseTypeFor term
  case ty of
    VSet l -> return tm
    v      -> raiseError p (ExpectingSet v)

{------------------------------------------------------------------------------}
-- Type checking
hasType :: (UsesIdentifiers ctxt, DefinitionContext ctxt) =>
           TermPos
        -> Value
        -> TypingMonad ctxt CS.Term

hasType (Annot p (Set l1)) (VSet l2) = do
  unless (l1 < l2) $ raiseError p (SetLevelMismatch l1 l2)
  return (In $ CS.Set l1)

hasType (Annot p (Set l1)) v = do
  raiseError p (TermIsASet v)

hasType (Annot p (Pi ident tA tB)) (VSet l) = do
  tmA  <- tA `hasType` VSet l
  vtmA <- eval tmA
  tmB  <- bindVar (fromMaybe "__x" ident) vtmA tB $ \_ tB -> tB `hasType` VSet l
  return (In $ CS.Pi (CS.Irrelevant ident) tmA tmB)

hasType (Annot p (Pi ident tA tB)) v = do
  raiseError p (TermIsASet v)

hasType (Annot p (Sigma ident tA tB)) (VSet l) = do
  tmA  <- tA `hasType` VSet l
  vtmA <- eval tmA
  tmB  <- bindVar (fromMaybe "__x" ident) vtmA tB $ \_ tB -> tB `hasType` VSet l
  return (In $ CS.Sigma (CS.Irrelevant ident) tmA tmB)

hasType (Annot p (Sigma ident tA tB)) v = do
  raiseError p (TermIsASet v)

hasType (Annot p (Sum t1 t2)) (VSet l) = do
  tm1 <- t1 `hasType` VSet l
  tm2 <- t2 `hasType` VSet l
  return (In $ CS.Sum tm1 tm2)

hasType (Annot p (Sum t1 t2)) v = do
  raiseError p (TermIsASet v)

hasType (Annot p (Unit tag)) (VSet l) = do
  return (In $ CS.Unit (CS.Irrelevant tag))

hasType (Annot p (Unit _)) v = do
  raiseError p (TermIsASet v)

hasType (Annot p Empty) (VSet l) = do
  return (In $ CS.Empty)

hasType (Annot p Empty) v = do
  raiseError p (TermIsASet v)

hasType (Annot p (Eq tA tB)) (VSet l) = do
  (tyA, tmA) <- synthesiseTypeFor tA
  (tyB, tmB) <- synthesiseTypeFor tB
  let tyA' = reifyType0 tyA
      tyB' = reifyType0 tyB
  -- FIXME: to do the in-universe version of this, we need to
  -- determine the level of tyA and tyB somehow, by checking tyA and
  -- tyB, which means converting from Checked syntax to
  -- LocallyNameless syntax. Also, we need to be able to do equality
  -- types for terms that aren't of synthesisable type.
  return (In $ CS.Eq tyA' tyB' tmA tmB)

hasType (Annot p (Eq tA tB)) v = do
  raiseError p (TermIsASet v)

hasType (Annot p (SemI tD x tA)) (VSet l) = do
  (tyD, tmD) <- synthesiseTypeFor tD
  case tyD of
    VIDesc tyI -> do
      tmA <- bindVar x tyI tA $ \x tA -> tA `hasType` (VSet l)
      let tmI = reifyType0 tyI
      return (In $ CS.SemI tmI tmD (CS.Irrelevant x) tmA)
    v ->
      raiseError (annot tD) (ExpectingIDesc v)

hasType (Annot p (SemI tD x tA)) v = do
  raiseError p (TermIsASet v)

hasType (Annot p (LiftI tD x tA i a tP tx)) (VSet l) = do
  (tyD, tmD) <- synthesiseTypeFor tD
  case tyD of
    VIDesc vI -> do
      tmA <- bindVar x vI tA $ \x tA -> hasType tA (VSet l)
      vA  <- evalA tmA
      tmP <- bindVar' 1 i vI tP $ \vi tP -> do
               bindVar a (vA [vi]) tP $ \va tP -> do
                 hasType tP (VSet l)
      vD <- eval tmD
      tmx <- tx `hasType` (vsemI vI vD x (\v -> vA [v]))
      let tmI = reifyType0 vI
      return (In $ CS.LiftI tmI tmD (CS.Irrelevant x) tmA (CS.Irrelevant i) (CS.Irrelevant a) tmP tmx)
    v -> do
      raiseError (annot tD) (ExpectingIDesc v)

hasType (Annot p (LiftI tD x tA i a tP tx)) v = do
  raiseError p (TermIsASet v)

hasType (Annot p (Group nm ab Nothing)) (VSet l) = do
  return (In $ CS.Group nm ab Nothing)

hasType (Annot p (Group nm ab Nothing)) v =  do
  raiseError p (TermIsASet v)

{------------------------------}
hasType (Annot p (Lam x tm)) (VPi _ tA tB) = do
  tm' <- bindVar x tA tm $ \x tm -> tm `hasType` (tB x)
  return (In $ CS.Lam (CS.Irrelevant x) tm')

hasType (Annot p (Lam x t)) v = do
  raiseError p (TermIsALambdaAbstraction v)


hasType (Annot p (Pair t1 t2)) (VSigma _ tA tB) = do
  tm1  <- t1 `hasType` tA
  vtm1 <- eval tm1
  tm2  <- t2 `hasType` (tB vtm1)
  return (In $ CS.Pair tm1 tm2)

hasType (Annot p (Pair _ _)) v = do
  raiseError p (TermIsAPairing v)


hasType (Annot p (Inl t)) (VSum tA _) = do
  tm <- t `hasType` tA
  return (In $ CS.Inl tm)

hasType (Annot p (Inl t)) v = do
  raiseError p (TermIsASumIntroduction v)

hasType (Annot p (Inr t)) (VSum _ tB) = do
  tm <- t `hasType` tB
  return (In $ CS.Inr tm)

hasType (Annot p (Inr t)) v = do
  raiseError p (TermIsASumIntroduction v)

hasType (Annot p UnitI) (VUnit tag) = do
  return (In $ CS.UnitI)

hasType (Annot p UnitI) v = do
  raiseError p (TermIsAUnitIntroduction v)


hasType (Annot p (Desc_K t)) VDesc = do
  tm <- t `hasType` (VSet 0)
  return (In $ CS.Desc_K tm)

hasType (Annot p (Desc_K t)) (VIDesc v) = do
  tm <- t `hasType` (VSet 0)
  return (In $ CS.IDesc_K tm)

hasType (Annot p (Desc_K t)) v = do
  raiseError p (TermIsADesc v)


hasType (Annot p Desc_Id) VDesc = do
  return (In $ CS.Desc_Id)

hasType (Annot p Desc_Id) v = do
  raiseError p (TermIsADesc v)


hasType (Annot p (Desc_Prod t1 t2)) VDesc = do
  tm1 <- t1 `hasType` VDesc
  tm2 <- t2 `hasType` VDesc
  return (In $ CS.Desc_Prod tm1 tm2)

hasType (Annot p (Desc_Prod t1 t2)) (VIDesc v) = do
  tm1 <- t1 `hasType` (VIDesc v)
  tm2 <- t2 `hasType` (VIDesc v)
  return (In $ CS.IDesc_Pair tm1 tm2)

hasType (Annot p (Desc_Prod t1 t2)) v = do
  raiseError p (TermIsADesc v)


hasType (Annot p (Desc_Sum t1 t2)) VDesc = do
  tm1 <- t1 `hasType` VDesc
  tm2 <- t2 `hasType` VDesc
  return (In $ CS.Desc_Sum tm1 tm2)

hasType (Annot p (Desc_Sum t1 t2)) v = do
  raiseError p (TermIsADesc v)


hasType (Annot p (Construct t)) (VMu f) = do
  tm <- t `hasType` (vsem f $$ VMu f)
  return (In $ CS.Construct (CS.Irrelevant Nothing) tm)

hasType (Annot p (Construct t)) (VMuI a d i) = do
  tm <- t `hasType` (vsemI a (d $$ i) "i" (vmuI a d $$))
  return (In $ CS.Construct (CS.Irrelevant Nothing) tm)

hasType (Annot p (Construct t)) v = do
  raiseError p (TermIsAConstruct v)


hasType (Annot p (IDesc_Id t)) (VIDesc v) = do
  tm <- t `hasType` v
  return (In $ CS.IDesc_Id tm)

hasType (Annot p (IDesc_Id t)) v = do
  raiseError p (TermIsADesc v)


hasType (Annot p (IDesc_Sg t1 t2)) (VIDesc v) = do
  tm1  <- t1 `hasType` (VSet 0)
  vtm1 <- eval tm1
  tm2  <- t2 `hasType` (vtm1 .->. VIDesc v)
  return (In $ CS.IDesc_Sg tm1 tm2)

hasType (Annot p (IDesc_Sg t1 t2)) v = do
  raiseError p (TermIsADesc v)

hasType (Annot p (IDesc_Pi t1 t2)) (VIDesc v) = do
  tm1  <- t1 `hasType` (VSet 0)
  vtm1 <- eval tm1
  tm2  <- t2 `hasType` (vtm1 .->. VIDesc v)
  return (In $ CS.IDesc_Pi tm1 tm2)

hasType (Annot p (IDesc_Pi t1 t2)) v = do
  raiseError p (TermIsADesc v)

hasType (Annot p (IDesc_Bind t1 x t2)) (VIDesc tyB) = do
  (ty1, tm1) <- synthesiseTypeFor t1
  case ty1 of
    VIDesc tyA -> do
      tm2 <- bindVar x tyA t2 $ \x t2 -> t2 `hasType` (VIDesc tyB)
      let tmA = reifyType0 tyA
          tmB = reifyType0 tyB
      return (In $ CS.IDesc_Bind tmA tmB tm1 (CS.Irrelevant x) tm2)
    v -> do
      raiseError (annot t1) (ExpectingIDesc v)

hasType (Annot p (IDesc_Bind t1 x t2)) v = do
  raiseError p (TermIsADesc v)


hasType (Annot p Refl) (VEq vA vB va vb) = do
  let tA = reifyType0 vA
      tB = reifyType0 vB
      ta = reify vA va 0
      tb = reify vB vb 0
  unless (tA == tB) $ do
    raiseError p (ReflCanOnlyProduceHomogenousEquality vA vB)
  unless (ta == tb) $ do
    raiseError p (ReflCanOnlyProduceEquality vA va vb)
  return (In $ CS.Refl)

hasType (Annot p Refl) v = do
  raiseError p (TermIsAnEquality v)


hasType (Annot p UserHole) v = do
  generateHole p Nothing (Just v)

{------------------------------------------------------------------------------}
-- The following are “high-level” features, and should be done using a general
-- elaborator
hasType (Annot p (NamedConstructor nm ts)) (VMuI vI vD vi) = do
  tag <- makeTag vI vD vi nm p
  let t = Annot p (Pair tag (makeConstructorArguments p ts))
  tm <- t `hasType` (vsemI vI (vD $$ vi) "i" (vmuI vI vD $$))
  return (In $ CS.Construct (CS.Irrelevant (Just nm)) tm)

hasType (Annot p (NamedConstructor nm ts)) v = do
  raiseError p (TermIsAConstruct v) -- FIXME: better error message?

hasType (Annot p (ElimEq t Nothing tp)) tP =
    do (ty, tm) <- synthesiseTypeFor t
       case ty of
         VEq vA vB va vb ->
             do let tA = reifyType0 vA
                    tB = reifyType0 vB
                unless (tA == tB) $ do
                  raiseError (annot t) (ExpectingHomogeneousEquality vA vB)
                let ta   = reify vA va 0
                    tb   = reify vB vb 0
                eq <- reify ty <$> eval tm <*> pure 0 -- normalise the equality proof
                let tmP  = reifyType0 tP
                    tmPg = CS.generalise [eq,tb] tmP
                vP'  <- tmPg `evalWith` [VRefl, va]
                tm_p <- tp `hasType` vP'
                return (In $ CS.ElimEq tA ta tb tm (CS.Irrelevant "a") (CS.Irrelevant "eq") tmPg tm_p)
         ty ->
             raiseError (annot t) (ExpectingEqualityType ty)

hasType (Annot p (ElimEmpty t1 Nothing)) v =
    do tm1     <- hasType t1 VEmpty
       let tm2 = reifyType0 v
       return (In $ CS.ElimEmpty tm1 tm2)

hasType (Annot p (Case t Nothing y tL z tR)) tP = do
  (tS,tmS) <- synthesiseTypeFor t
  case tS of
    VSum tA tB ->
        do tmS' <- reify tS <$> eval tmS <*> pure 0
           let tmP = CS.generalise [tmS'] $ reifyType0 tP
           tmL <- bindVar y tA tL $ \y tL -> do
                    vP <- tmP `evalWith` [VInl y]
                    tL `hasType` vP
           tmR <- bindVar z tB tR $ \z tR -> do
                    vP <- tmP `evalWith` [VInr z]
                    tR `hasType` vP
           let tmA = reifyType0 tA
               tmB = reifyType0 tB
           return (In $ CS.Case tmS tmA tmB (CS.Irrelevant "x") tmP (CS.Irrelevant y) tmL (CS.Irrelevant z) tmR)
    v ->
        do raiseError (annot t) (ExpectingSumType v)

hasType (Annot p (Eliminate t Nothing inm xnm pnm tK)) vty = do
  (ty,tm) <- synthesiseTypeFor t
  (vI, vDesc, vi) <-
      case ty of
        VMuI vI vDesc vi ->
            return (vI, vDesc, vi)
        _                ->
            raiseError (annot t) (OtherError "expecting a term of recursive type")
  -- generate the elimination type
  -- FIXME: this does not work when the index is a pair, and 'vty' refers to the parts separately
  -- need to make a better 'generalise' that can spot that the term being generalised over is a tuple
  -- see interpreter.fv, definitions "lookup" and "eval"
  tmi <- return (reify vI vi 0)
  tm' <- reify ty <$> eval tm <*> pure 0
  let tmP = CS.generalise [tm',tmi] $ reifyType0 vty
  -- check the algebra
  vP  <- evalA tmP
  tmK <- bindVar' 2 inm vI tK $ \i tK ->
         bindVar' 1 xnm (vsemI vI (vDesc $$ i) "i" (vmuI vI vDesc $$)) tK $ \x tK ->
         bindVar' 0 pnm (vliftI vI (vDesc $$ i) "i" (vmuI vI vDesc $$) "i" "a" (\i a -> vP [a,i]) x) tK $ \p tK ->
         tK `hasType` (vP [VConstruct Nothing x,i])
  vtm <- eval tm
  let tyI  = reifyType0 vI
      desc = reify (vI .->. VIDesc vI) vDesc 0
  return ( In $ CS.Eliminate tyI desc tmi tm
                             (CS.Irrelevant "i") (CS.Irrelevant "x") tmP
                             (CS.Irrelevant inm) (CS.Irrelevant xnm) (CS.Irrelevant pnm) tmK)

-- this is an application, where we are pushing a type in instead of
-- having it inferred. This means we have to guess what the function
-- type is. FIXME: this should generate a term with a type ascription
-- in it.
hasType (Annot p (Generalise t1 t2)) v = do
  (ty1,tm1) <- synthesiseTypeFor t1
  tm1normalised <- reify ty1 <$> eval tm1 <*> pure 0
  v' <- evalA (CS.generalise [tm1normalised] $ reifyType0 v)
  tm2 <- t2 `hasType` (forall "x" ty1 $ \x -> v' [x])
  return (In $ CS.App tm2 tm1)

hasType (Annot p (CasesOn isRecursive x clauses)) v = do
  (ty,_) <- synthesiseTypeFor x
  constructorInfo <-
      case ty of
        VMuI vI vD vi -> getDatatypeInfo vI vD vi p
        _ -> raiseError p (OtherError "cannot do cases on non-inductive datatype")

  let makeClausesMap [] m = return m
      makeClausesMap ((ident,patterns,tm):clauses) m =
          if M.member ident m then
              raiseError p (OtherError $ "duplicate constructor names: " ++ show ident)
          else
              makeClausesMap clauses (M.insert ident (patterns,tm) m)

  let mkPattern []           []                   =
          do return ([BindNull], [BindNull]) -- for the index equality proof
      mkPattern (True:args)  (PatVar nm:patterns) =
          do (argPats,recPats) <- mkPattern args patterns
             return (BindVar nm:argPats, BindRecur nm:recPats)
      mkPattern (True:args)  (PatNull:patterns) =
          do (argPats,recPats) <- mkPattern args patterns
             return (BindNull:argPats, BindNull:recPats)
      mkPattern (True:args)  (PatTuple _:patterns) =
          do raiseError p (OtherError "pattern match for recursive arguments must be plain variables")
      mkPattern (False:args) (pat:patterns) =
          do (argPats,recPats) <- mkPattern args patterns
             return (bindingOfPattern pat:argPats, recPats)

  let mkEqRef []    = Annot p (Bound 1)
      mkEqRef (_:l) = Annot p (Proj2 (mkEqRef l))

  let doCase ident args clausesMap bindings =
          do (patterns,tm) <- case M.lookup ident clausesMap of
                                Nothing -> raiseError p (OtherError $ "constructor " ++ show ident ++ " not handled")
                                Just x  -> return x
             (argPats, recPats) <- mkPattern args patterns
             
             let bindings' =
                     (if isRecursive then BindTuple recPats else BindNull):BindTuple argPats:bindings

             return ( Annot p $ Lam "d" $ -- the data
                      Annot p $ Lam "r" $ -- the possible recursive calls
                      Annot p $ ElimEq (mkEqRef patterns) Nothing $
                      tm bindings'
                    , M.delete ident clausesMap)

  let doCases [] clausesMap discrimVar bindings =
          do return (Annot p $ ElimEmpty discrimVar Nothing, clausesMap)
      doCases [(ident,args)] clausesMap discrimVar bindings =
          do doCase ident args clausesMap bindings
      doCases ((ident,args):idents) clausesMap discrimVar bindings =
          do let bindings' = BindNull:bindings
             (thisCase,clausesMap')   <- doCase  ident args clausesMap bindings'
             (otherCases,clausesMap'') <- doCases idents clausesMap' (Annot p (Bound 0)) bindings'
             return (Annot p $ Case discrimVar Nothing "u" thisCase "u" otherCases, clausesMap'')

  let basicBindings = [BindNull,BindNull,BindNull] -- the three things bound by the 'eliminate' construct
      discrimVar    = Annot p (Proj1 (Annot p (Bound 1)))
  clausesMap          <- makeClausesMap clauses M.empty
  (cases,clausesMap') <- doCases constructorInfo clausesMap discrimVar basicBindings

  unless (M.size clausesMap' == 0) $ do
    raiseError p (OtherError $ "extra cases supplied")

  let desugared =
          Annot p $ Eliminate x Nothing "i" "x" "r" $
          Annot p $ Generalise (Annot p (Bound 0)) $
          Annot p $ Generalise (Annot p (Proj2 (Annot p (Bound 1)))) $
          cases

  desugared `hasType` v

{------------------------------}
{- Built-in group operations -}

hasType (Annot p GroupUnit) (VGroup nm ab _) = do
  return (In $ CS.GroupUnit)

hasType (Annot p GroupUnit) v = do
  raiseError p (TermIsAGroupExpression v)

hasType (Annot p (GroupMul t1 t2)) (VGroup nm ab ty) = do
  tm1 <- hasType t1 (VGroup nm ab ty)
  tm2 <- hasType t2 (VGroup nm ab ty)
  return (In $ CS.GroupMul tm1 tm2)

hasType (Annot p (GroupMul t1 t2)) v = do
  raiseError p (TermIsAGroupExpression v)

hasType (Annot p (GroupInv t)) (VGroup nm ab ty) = do
  tm <- hasType t (VGroup nm ab ty)
  return (In $ CS.GroupInv tm)

hasType (Annot p (GroupInv t)) v = do
  raiseError p (TermIsAGroupExpression v)

{------------------------------}
{- Fall through case -}
hasType (Annot p t) v = do
  (v',tm) <- synthesiseTypeFor (Annot p t)
  compareTypes p v v'
  return tm

{------------------------------------------------------------------------------}
{------------------------------------------------------------------------------}
{------------------------------------------------------------------------------}
-- Attempt to synthesise a type for a given term. It is guaranteed
-- that the returned type and term will be well-typed in the supplied
-- context.
synthesiseTypeFor :: (UsesIdentifiers ctxt, DefinitionContext ctxt) =>
                     TermPos
                  -> TypingMonad ctxt (Value, CS.Term)

synthesiseTypeFor (Annot p (Bound _)) =
    error "internal: 'bound' variable discovered during type synthesis"

synthesiseTypeFor (Annot p (Free nm globalFlag)) = do
  result <- lookupIdent nm globalFlag
  case result of
    Nothing -> raiseError p (UnknownIdentifier nm)
    Just tA -> return (tA, In $ CS.Free nm)

synthesiseTypeFor (Annot p (App t t')) = do
  (tF, tm) <- synthesiseTypeFor t
  case tF of
    VPi _ tA tB -> do tm'  <- t' `hasType` tA
                      vtm' <- eval tm'
                      return (tB vtm', In $ CS.App tm tm')
    ty          -> do raiseError p (ExpectingPiType ty)

synthesiseTypeFor (Annot p (Case t (Just (x, tP)) y tL z tR)) = do
  (tS,tmS) <- synthesiseTypeFor t
  case tS of
    VSum tA tB ->
        do tmP <- bindVar x tS tP $ \_ tP -> isType tP
           tmL <- bindVar y tA tL $ \y tL -> do
                    vP <- tmP `evalWith` [VInl y]
                    tL `hasType` vP
           tmR <- bindVar z tB tR $ \z tR -> do
                    vP <- tmP `evalWith` [VInr z]
                    tR `hasType` vP
           vS  <- eval tmS
           v   <- tmP `evalWith` [vS]
           let tmA = reifyType0 tA
               tmB = reifyType0 tB
           return (v, In $ CS.Case tmS tmA tmB (CS.Irrelevant x) tmP (CS.Irrelevant y) tmL (CS.Irrelevant z) tmR)
    v -> do
      raiseError (annot t) (ExpectingSumType v)

synthesiseTypeFor (Annot p (ElimEmpty t1 (Just t2))) = do
  tm1  <- t1 `hasType` VEmpty
  tm2  <- isType t2
  vtm2 <- eval tm2
  return (vtm2, In $ CS.ElimEmpty tm1 tm2)

synthesiseTypeFor (Annot p (ElimEq t (Just (a, e, tP)) tp)) = do
  (ty, tm) <- synthesiseTypeFor t
  case ty of
    VEq vA vB va vb ->
        do let tA = reifyType0 vA
               tB = reifyType0 vB
           unless (tA == tB) $ do
             raiseError p (ExpectingHomogeneousEquality vA vB)
           -- check the elimination set
           tmP <- bindVar' 1 a vA tP $ \x tP -> do
                    bindVar e (VEq vA vA va x) tP $ \e tP -> do
                      isType tP
           -- Check 'tp'
           vtmP  <- tmP `evalWith` [VRefl, va]
           tm_p  <- tp `hasType` vtmP
           -- create the result type
           vtm   <- eval tm
           vtmP' <- tmP `evalWith` [vtm, vb]
           -- create the term
           let ta = reify vA va 0
               tb = reify vB vb 0
           return (vtmP', In $ CS.ElimEq tA ta tb tm (CS.Irrelevant a) (CS.Irrelevant e) tmP tm_p)
    ty ->
        do raiseError (annot t) (ExpectingEqualityType ty)

synthesiseTypeFor (Annot p Desc) = do
  return (VSet 1, In $ CS.Desc)

synthesiseTypeFor (Annot p Desc_Elim) = do
  return ( forall "P" (VDesc .->. VSet 10) $ \vP ->
           (forall "A" (VSet 0) $ \x -> vP $$ VDesc_K x) .->.
           (vP $$ VDesc_Id) .->.
           (forall "d1" VDesc $ \d1 ->
            forall "d2" VDesc $ \d2 ->
            (vP $$ d1) .->. (vP $$ d2) .->. (vP $$ (VDesc_Prod d1 d2))) .->.
           (forall "d1" VDesc $ \d1 ->
            forall "d2" VDesc $ \d2 ->
            (vP $$ d1) .->. (vP $$ d2) .->. (vP $$ (VDesc_Sum d1 d2))) .->.
           (forall "x" VDesc $ \x -> vP $$ x)
         , In $ CS.Desc_Elim)

synthesiseTypeFor (Annot p Sem) = do
  return ( VDesc .->. VSet 0 .->. VSet 0, In $ CS.Sem )

synthesiseTypeFor (Annot p (Mu t)) = do
  tm <- t `hasType` VDesc
  return (VSet 0, In $ CS.Mu tm)

synthesiseTypeFor (Annot p (MuI t1 t2)) = do
  tm1 <- t1 `hasType` (VSet 0)
  v   <- eval tm1
  tm2 <- t2 `hasType` (v .->. VIDesc v)
  return (v .->. VSet 0, In $ CS.MuI tm1 tm2)

synthesiseTypeFor (Annot p Induction) = do
  return ( forall "F" VDesc               $ \f ->
           forall "P" (VMu f .->. VSet 2) $ \p ->
           (forall "x" (vsem f $$ VMu f) $ \x ->
            (vlift $$ f $$ VMu f $$ p $$ x) .->.
            p $$ (VConstruct Nothing x)) .->.
           (forall "x" (VMu f) $ \x -> p $$ x)
         , In CS.Induction)

synthesiseTypeFor (Annot p (Proj1 t)) = do
  (tP, tmP) <- synthesiseTypeFor t
  case tP of
    VSigma _ tA _ -> do return (tA, In $ CS.Proj1 tmP)
    v             -> do raiseError p (Proj1FromNonSigma v)

synthesiseTypeFor (Annot p (Proj2 t)) = do
  (tP, tmP) <- synthesiseTypeFor t
  case tP of
    VSigma _ _ tB -> do v <- vfst <$> eval tmP
                        return (tB v, In $ CS.Proj2 tmP)
    v             -> do raiseError p (Proj2FromNonSigma v)

{------------------------------------------------------------------------------}
-- Descriptions of indexed types
synthesiseTypeFor (Annot p IDesc) = do
  return (VSet 0 .->. VSet 1, In $ CS.IDesc)

synthesiseTypeFor (Annot p (MapI tD i1 tA i2 tB tf tx)) = do
  (tyD, tmD) <- synthesiseTypeFor tD
  case tyD of
    VIDesc tyI -> do
      let tmI = reifyType0 tyI
      tmA <- bindVar i1 tyI tA $ \_ tA -> isType tA
      tmB <- bindVar i2 tyI tB $ \_ tB -> isType tB
      vA <- evalA tmA
      vB <- evalA tmB
      vD <- eval tmD
      tmf <- tf `hasType` (forall i1 tyI $ \vi -> vA [vi] .->. vB [vi])
      tmx <- tx `hasType` (vsemI tyI vD i1 (\v -> vA [v]))
      return ( vsemI tyI vD i2 (\v -> vB [v])
             , In $ CS.MapI tmI tmD (CS.Irrelevant i1) tmA (CS.Irrelevant i2) tmB tmf tmx )
    v ->
        raiseError (annot tD) (ExpectingIDesc v)

synthesiseTypeFor (Annot p IDesc_Elim) = do
  return ( forall "I" (VSet 0) $ \i ->
           forall "P" (VIDesc i .->. VSet 10) $ \p ->
           (forall "x" i $ \x -> p $$ VIDesc_Id x) .->.
           (forall "A" (VSet 0) $ \a -> p $$ VIDesc_K a) .->.
           (forall "D1" (VIDesc i) $ \d1 ->
            forall "D2" (VIDesc i) $ \d2 ->
            (p $$ d1) .->.
            (p $$ d2) .->.
            (p $$ (VIDesc_Pair d1 d2))) .->.
           (forall "A" (VSet 0) $ \a ->
            forall "D" (a .->. VIDesc i) $ \d ->
            (forall "x" a $ \x -> p $$ (d $$ x)) .->.
            (p $$ (VIDesc_Sg a d))) .->.
           (forall "A" (VSet 0) $ \a ->
            forall "D" (a .->. VIDesc i) $ \d ->
            (forall "x" a $ \x -> p $$ (d $$ x)) .->.
            (p $$ (VIDesc_Pi a d))) .->.
           (forall "D" (VIDesc i) $ \d -> p $$ d)
         , In $ CS.IDesc_Elim)

synthesiseTypeFor (Annot p InductionI) = do
  return ( forall "I" (VSet 0) $ \vI ->
           forall "D" (vI .->. VIDesc vI) $ \vD ->
           forall "P" (forall "i" vI $ \i -> (vmuI vI vD $$ i) .->. VSet 2) $ \vP ->
           forall "k" (forall "i" vI $ \i ->
                       forall "x" (vsemI vI (vD $$ i) "i" (vmuI vI vD $$)) $ \x ->
                       (vliftI vI (vD $$ i) "i" (vmuI vI vD $$) "i" "a" (\i a -> vP $$ i $$ a) x) .->.
                       (vP $$ i $$ VConstruct Nothing x)) $ \k ->
           forall "i" vI $ \i ->
           forall "x" (vmuI vI vD $$ i) $ \x ->
           vP $$ i $$ x
         , In $ CS.InductionI)

synthesiseTypeFor (Annot p (Eliminate t (Just (i,x,tP)) inm xnm pnm tK)) = do
  (ty,tm) <- synthesiseTypeFor t
  (vI, vDesc, vi) <-
      case ty of
        VMuI vI vDesc vi ->
            return (vI, vDesc, vi)
        _                ->
            raiseError (annot t) (OtherError "expecting a term of recursive type")
  -- check the elimination type
  tmP <- bindVar' 1 i vI tP $ \i tP ->
         bindVar x (VMuI vI vDesc i) tP $ \x tP ->
         isType tP
  -- check the algebra
  vP  <- evalA tmP
  tmK <- bindVar' 2 inm vI tK $ \i tK ->
         bindVar' 1 xnm (vsemI vI (vDesc $$ i) "i" (vmuI vI vDesc $$)) tK $ \x tK ->
         bindVar' 0 pnm (vliftI vI (vDesc $$ i) "i" (vmuI vI vDesc $$) "i" "a" (\i a -> vP [a,i]) x) tK $ \p tK ->
         tK `hasType` (vP [VConstruct Nothing x,i])
  vtm <- eval tm
  let tyI  = reifyType0 vI
      desc = reify (vI .->. VIDesc vI) vDesc 0
      tmi  = reify vI vi 0
  return ( vP [vtm,vi]
         , In $ CS.Eliminate tyI desc tmi tm
                             (CS.Irrelevant i) (CS.Irrelevant x) tmP
                             (CS.Irrelevant inm) (CS.Irrelevant xnm) (CS.Irrelevant pnm) tmK)

synthesiseTypeFor (Annot p (Group nm ab (Just ty))) = do
  tyTm <- ty `hasType` VSet 0
  vty  <- eval tyTm
  return (vty .->. VSet 0, In $ CS.Group nm ab (Just tyTm))

-- FIXME: synthesise Set0 for (Group nm ab Nothing)?

synthesiseTypeFor (Annot p (GroupMul t1 t2)) = do
  (ty1, tm1) <- synthesiseTypeFor t1
  (ty2, tm2) <- synthesiseTypeFor t2
  case ty1 of
    VGroup nm1 ab1 vparam1 ->
        case ty2 of
          VGroup nm2 ab2 vparam2 -> do
              let param1 = fmap (\(vty,vtm) -> (reifyType0 vty, reify vty vtm 0)) vparam1
                  param2 = fmap (\(vty,vtm) -> (reifyType0 vty, reify vty vtm 0)) vparam2
              if nm1 == nm2 && ab1 == ab2 && param1 == param2 then
                  return (VGroup nm1 ab1 vparam1, In $ CS.GroupMul tm1 tm2)
              else
                  raiseError p (OtherError "Groups not equal")
          _ ->
              raiseError (annot t2) (OtherError "Right operand not a group element")
    _ ->
        raiseError (annot t1) (OtherError "Left operand not a group element")

synthesiseTypeFor (Annot p (GroupInv t)) = do
  (ty, tm) <- synthesiseTypeFor t
  case ty of
    VGroup nm ab vparam ->
        return (VGroup nm ab vparam, In $ CS.GroupInv tm)
    _ ->
        raiseError (annot t) (OtherError "Operand is not a group element")

--------------------------------------------------------------------------------
-- Type ascription
synthesiseTypeFor (Annot p (TypeAscrip t ty)) = do
  ty1 <- isType ty
  vty <- eval ty1
  tm  <- t `hasType` vty
  return (vty, tm)

--------------------------------------------------------------------------------
synthesiseTypeFor (Annot p t) = do
  raiseError p (UnableToSynthesise (Annot p t))
