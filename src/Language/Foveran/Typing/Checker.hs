{-# LANGUAGE OverloadedStrings, TypeOperators #-}

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
import           Data.Rec (AnnotRec (Annot), Rec (In))
import           Text.Position (Span)
import           Language.Foveran.Syntax.Identifier (Ident, UsesIdentifiers (..), freshFor)
import           Language.Foveran.Syntax.LocallyNameless (TermPos, TermCon (..), close)
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
            -> TypingMonad ctxt (Maybe Value)
lookupIdent ident =
    lookupType ident <$> getFullContext

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

{------------------------------------------------------------------------------}
compareTypes :: Span -> Value -> Value -> TypingMonad ctxt ()
compareTypes p v1 v2 =
    do let tm1 = reifyType0 v1
           tm2 = reifyType0 v2
       unless (CS.cmp (<=) tm2 tm1) $ do raiseError p (TypesNotEqual v1 v2)

-- should probably extend the cummulativity checking to include Pi and
-- Sigma types (i.e. with cummulativity in the codomain of Pi). See
-- e.g. “The View from the Left” or Norell's thesis.

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
  tmB  <- bindVar (fromMaybe "x" ident) vtmA tB $ \_ tB -> isType tB
  return (In $ CS.Pi ident tmA tmB)
isType (Annot p (Sigma ident tA tB)) = do
  tmA  <- isType tA
  vtmA <- eval tmA
  tmB  <- bindVar (fromMaybe "x" ident) vtmA tB $ \_ tB -> isType tB
  return (In $ CS.Sigma ident tmA tmB)
isType (Annot p (Sum t1 t2)) = do
  tm1 <- isType t1
  tm2 <- isType t2
  return (In $ CS.Sum tm1 tm2)
isType (Annot p Unit) = do
  return (In $ CS.Unit)
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
      return (In $ CS.SemI tmI tmD x tmA)
    v ->
      raiseError p (ExpectingIDescForSemI v)
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
      return (In $ CS.LiftI tmI tmD x tmA i a tmP tmx)
    v ->
        raiseError p (ExpectingIDescForSemI v) -- FIXME: more specific error message
isType (Annot p UserHole) = do
  generateHole p Nothing Nothing
isType term@(Annot p _) = do
  (ty,tm) <- synthesiseTypeFor term
  case ty of
    VSet l -> return tm
    _      -> raiseError p ExpectingSet

{------------------------------------------------------------------------------}
-- Type checking
hasType :: (UsesIdentifiers ctxt, DefinitionContext ctxt) =>
           TermPos
        -> Value
        -> TypingMonad ctxt CS.Term

hasType (Annot p (Set l1)) (VSet l2) = do
  unless (l1 < l2) $ raiseError p ExpectingSet -- FIXME: expecting a set of a certain level
  return (In $ CS.Set l1)

hasType (Annot p (Pi ident tA tB)) (VSet l) = do
  tmA  <- tA `hasType` VSet l
  vtmA <- eval tmA
  tmB  <- bindVar (fromMaybe "x" ident) vtmA tB $ \_ tB -> tB `hasType` VSet l
  return (In $ CS.Pi ident tmA tmB)

hasType (Annot p (Sigma ident tA tB)) (VSet l) = do
  tmA  <- tA `hasType` VSet l
  vtmA <- eval tmA
  tmB  <- bindVar (fromMaybe "x" ident) vtmA tB $ \_ tB -> tB `hasType` VSet l
  return (In $ CS.Sigma ident tmA tmB)

hasType (Annot p (Sum t1 t2)) (VSet l) = do
  tm1 <- t1 `hasType` VSet l
  tm2 <- t2 `hasType` VSet l
  return (In $ CS.Sum tm1 tm2)

hasType (Annot p Unit) (VSet l) = do
  return (In $ CS.Unit)

hasType (Annot p Empty) (VSet l) = do
  return (In $ CS.Empty)

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

hasType (Annot p (SemI tD x tA)) (VSet l) = do
  (tyD, tmD) <- synthesiseTypeFor tD
  case tyD of
    VIDesc tyI -> do
      tmA <- bindVar x tyI tA $ \x tA -> tA `hasType` (VSet l)
      let tmI = reifyType0 tyI
      return (In $ CS.SemI tmI tmD x tmA)
    v ->
      raiseError p (ExpectingIDescForSemI v)

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
      return (In $ CS.LiftI tmI tmD x tmA i a tmP tmx)
    v ->
        raiseError p (ExpectingIDescForSemI v) -- FIXME: more specific error message

-- FIXME: all the error cases for Set too.

{------------------------------}
hasType (Annot p (Lam x tm)) (VPi _ tA tB) = do
  tm' <- bindVar x tA tm $ \x tm -> tm `hasType` (tB x)
  return (In $ CS.Lam x tm')

hasType (Annot p (Lam x t)) v = do
  raiseError p (ExpectingPiTypeForLambda v)


hasType (Annot p (Pair t1 t2)) (VSigma _ tA tB) = do
  tm1  <- t1 `hasType` tA
  vtm1 <- eval tm1
  tm2  <- t2 `hasType` (tB vtm1)
  return (In $ CS.Pair tm1 tm2)

hasType (Annot p (Pair _ _)) v = do
  raiseError p (ExpectingSigmaTypeForPair v)


hasType (Annot p (Inl t)) (VSum tA _) = do
  tm <- t `hasType` tA
  return (In $ CS.Inl tm)

hasType (Annot p (Inl t)) v = do
  raiseError p (ExpectingSumTypeForInl v)

hasType (Annot p (Inr t)) (VSum _ tB) = do
  tm <- t `hasType` tB
  return (In $ CS.Inr tm)

hasType (Annot p (Inr t)) v = do
  raiseError p (ExpectingSumTypeForInr v)

hasType (Annot p UnitI) VUnit = do
  return (In $ CS.UnitI)

hasType (Annot p UnitI) v = do
  raiseError p (ExpectingUnitTypeForUnit v)


hasType (Annot p (Desc_K t)) VDesc = do
  tm <- t `hasType` (VSet 0)
  return (In $ CS.Desc_K tm)

hasType (Annot p (Desc_K t)) (VIDesc v) = do
  tm <- t `hasType` (VSet 0)
  return (In $ CS.IDesc_K tm)

hasType (Annot p (Desc_K t)) v = do
  raiseError p (ExpectingDescTypeForDesc v)


hasType (Annot p Desc_Id) VDesc = do
  return (In $ CS.Desc_Id)

hasType (Annot p Desc_Id) v = do
  raiseError p (ExpectingDescTypeForDesc v)


hasType (Annot p (Desc_Prod t1 t2)) VDesc = do
  tm1 <- t1 `hasType` VDesc
  tm2 <- t2 `hasType` VDesc
  return (In $ CS.Desc_Prod tm1 tm2)

hasType (Annot p (Desc_Prod t1 t2)) (VIDesc v) = do
  tm1 <- t1 `hasType` (VIDesc v)
  tm2 <- t2 `hasType` (VIDesc v)
  return (In $ CS.IDesc_Pair tm1 tm2)

hasType (Annot p (Desc_Prod t1 t2)) v = do
  raiseError p (ExpectingDescTypeForDesc v)


hasType (Annot p (Desc_Sum t1 t2)) VDesc = do
  tm1 <- t1 `hasType` VDesc
  tm2 <- t2 `hasType` VDesc
  return (In $ CS.Desc_Sum tm1 tm2)

hasType (Annot p (Desc_Sum t1 t2)) v = do
  raiseError p (ExpectingDescTypeForDesc v)


hasType (Annot p (Construct t)) (VMu f) = do
  tm <- t `hasType` (vsem f $$ VMu f)
  return (In $ CS.Construct tm)

hasType (Annot p (Construct t)) (VMuI a d i) = do
  tm <- t `hasType` (vsemI a (d $$ i) "i" (vmuI a d $$))
  return (In $ CS.Construct tm)

hasType (Annot p (Construct t)) v = do
  raiseError p (ExpectingMuTypeForConstruct v)


hasType (Annot p (IDesc_Id t)) (VIDesc v) = do
  tm <- t `hasType` v
  return (In $ CS.IDesc_Id tm)

hasType (Annot p (IDesc_Id t)) v = do
  raiseError p (ExpectingDescTypeForDesc v)


hasType (Annot p (IDesc_Sg t1 t2)) (VIDesc v) = do
  tm1  <- t1 `hasType` (VSet 0)
  vtm1 <- eval tm1
  tm2  <- t2 `hasType` (vtm1 .->. VIDesc v)
  return (In $ CS.IDesc_Sg tm1 tm2)

hasType (Annot p (IDesc_Sg t1 t2)) v = do
  raiseError p (ExpectingDescTypeForDesc v)

hasType (Annot p (IDesc_Pi t1 t2)) (VIDesc v) = do
  tm1  <- t1 `hasType` (VSet 0)
  vtm1 <- eval tm1
  tm2  <- t2 `hasType` (vtm1 .->. VIDesc v)
  return (In $ CS.IDesc_Pi tm1 tm2)

hasType (Annot p (IDesc_Pi t1 t2)) v = do
  raiseError p (ExpectingDescTypeForDesc v)

hasType (Annot p (IDesc_Bind t1 x t2)) (VIDesc tyB) = do
  (ty1, tm1) <- synthesiseTypeFor t1
  case ty1 of
    VIDesc tyA -> do
      tm2 <- bindVar x tyA t2 $ \x t2 -> t2 `hasType` (VIDesc tyB)
      let tmA = reifyType0 tyA
          tmB = reifyType0 tyB
      return (In $ CS.IDesc_Bind tmA tmB tm1 x tm2)
    v ->
        raiseError p (ExpectingDescTypeForDesc v) -- FIXME: better error message, and position

hasType (Annot p (IDesc_Bind t1 x t2)) v = do
  raiseError p (ExpectingDescTypeForDesc v)


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
  raiseError p (ReflExpectingEqualityType v)

hasType (Annot p UserHole) v = do
  generateHole p Nothing (Just v)

{------------------------------------------------------------------------------}
-- The following are “high-level” features, and should be done using a general
-- elaborator
hasType (Annot p (ElimEq t Nothing tp)) tP =
    do (ty, tm) <- synthesiseTypeFor t
       case ty of
         VEq vA vB va vb ->
             do let tA = reifyType0 vA
                    tB = reifyType0 vB
                unless (tA == tB) $ do
                  raiseError p (ElimEqCanOnlyHandleHomogenousEq vA vB)
                let ta   = reify vA va 0
                    tb   = reify vB vb 0
                eq <- reify ty <$> eval tm <*> pure 0 -- normalise the equality proof
                let tmP  = reifyType0 tP
                    tmPg = CS.generalise [eq,tb] tmP
                vP'  <- tmPg `evalWith` [VRefl, va]
                tm_p <- tp `hasType` vP'
                return (In $ CS.ElimEq tA ta tb tm "a" "eq" tmPg tm_p)
         ty ->
             raiseError p (ExpectingEqualityType ty)


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
           return (In $ CS.Case tmS tmA tmB "x" tmP y tmL z tmR)
    v ->
        do raiseError p (CaseOnNonSum v)


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

synthesiseTypeFor (Annot p (Free nm)) = do
  result <- lookupIdent nm
  case result of
    Nothing -> raiseError p (UnknownIdentifier nm)
    Just tA -> return (tA, In $ CS.Free nm)

synthesiseTypeFor (Annot p (App t t')) = do
  (tF, tm) <- synthesiseTypeFor t
  case tF of
    VPi _ tA tB -> do tm'  <- t' `hasType` tA
                      vtm' <- eval tm'
                      return (tB vtm', In $ CS.App tm tm')
    ty          -> do raiseError p (ApplicationOfNonFunction ty)

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
           return (v, In $ CS.Case tmS tmA tmB x tmP y tmL z tmR)
    v ->
        do raiseError p (CaseOnNonSum v)

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
             raiseError p (ElimEqCanOnlyHandleHomogenousEq vA vB)
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
           return (vtmP', In $ CS.ElimEq tA ta tb tm a e tmP tm_p)
    ty ->
        do raiseError p (ExpectingEqualityType ty)

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
            p $$ (VConstruct x)) .->.
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

-- FIXME: hack, to get the datatype descriptions going
synthesiseTypeFor (Annot p UnitI) = do
  return (VUnit, In $ CS.UnitI)

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
             , In $ CS.MapI tmI tmD i1 tmA i2 tmB tmf tmx )
    v ->
        raiseError p (ExpectingIDescForSemI v)

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
                       (vP $$ i $$ VConstruct x)) $ \k ->
           forall "i" vI $ \i ->
           forall "x" (vmuI vI vD $$ i) $ \x ->
           vP $$ i $$ x
         , In $ CS.InductionI)

synthesiseTypeFor (Annot p t) = do
  raiseError p (UnableToSynthesise (Annot p t))
