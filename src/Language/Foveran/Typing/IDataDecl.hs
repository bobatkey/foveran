{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.IDataDecl
    ( processIDataDecl )
    where

import qualified Data.Set as S
import           Control.Monad (unless, guard, when, forM_)
import           Control.Monad.State (StateT, evalStateT, get, put, lift)
import           Data.Maybe (fromMaybe)
import           Data.Rec (AnnotRec (Annot))
import           Language.Foveran.Typing.DeclCheckMonad
import           Language.Foveran.Typing.Errors
import           Language.Foveran.Syntax.Display
import           Language.Foveran.Syntax.Identifier ((<+>))
import qualified Language.Foveran.Syntax.LocallyNameless as LN
import           Text.Position (Span (..), makeSpan)

--------------------------------------------------------------------------------
(@|) p t = Annot p t

--------------------------------------------------------------------------------
processIDataDecl :: IDataDecl -> DeclCheckM ()
processIDataDecl d = do
  evalStateT (forM_ (dataParameters d) checkParameterName) S.empty

  -- Check the constructors for duplicate names, shadowing and
  -- correctness of parameter names. Does not check for any type
  -- correctness.
  evalStateT (forM_ (dataConstructors d) (checkConstructor d)) S.empty

  -- Generate the description of this datatype
  let codeName = dataName d <+> ":code"
      codeType = paramsType   (dataParameters d) [] (descType d)
      code     = paramsLambda (dataParameters d) [] (makeCode d)
  checkInternalDefinition (dataPos d) codeName codeType (Just code)

  -- Generate the type itself
  let typ = paramsType   (dataParameters d) [] (makeMuTy d)
      trm = paramsLambda (dataParameters d) [] (makeMu d)
  checkInternalDefinition (dataPos d) (dataName d) typ (Just trm)

  -- Generate the functions for each of the constructors
  makeConstructors d id (dataConstructors d)

--------------------------------------------------------------------------------
checkParameterName :: DataParameter ->
                      StateT (S.Set Ident) DeclCheckM ()
checkParameterName (DataParameter pos paramName _) = do
  usedNames <- get
  when (paramName `S.member` usedNames) $ lift $ reportError pos (DuplicateParameterName paramName)
  put (S.insert paramName usedNames)

--------------------------------------------------------------------------------
checkConstructor :: IDataDecl ->
                    IConstructor ->
                    StateT (S.Set Ident) DeclCheckM ()
checkConstructor d (IConstructor p nm components) = do
  usedNames <- get
  when (nm `S.member` usedNames) $ lift $ reportError p (DuplicateConstructorName nm)
  lift $ checkConstructorsBits d components
  put (S.insert nm usedNames)

snd3 (_,b,_) = b -- FIXME: remove this

checkConstructorsBits :: IDataDecl ->
                         IConstructorBitsPos ->
                         DeclCheckM ()
checkConstructorsBits d (Annot p (ConsPi nm t bits)) = do
  when (nm == dataName d) $ reportError p ShadowingDatatypeName
  when (nm `elem` (map paramIdent $ dataParameters d)) $ reportError p ShadowingParameterName
  checkConstructorsBits d bits
checkConstructorsBits d (Annot p (ConsArr t bits)) = do
  -- FIXME: extract the recursive call if it exists and check to see
  -- whether it properly uses the parameter names
  checkConstructorsBits d bits
checkConstructorsBits d (Annot p (ConsEnd nm ts)) = do
  unless (nm == dataName d) $ reportError p (ConstructorTypesMustEndWithNameOfDatatype nm (dataName d))
  checkParameters p ts (map paramIdent $ dataParameters d)

checkParameters :: Span -> [TermPos] -> [Ident] -> DeclCheckM ()
checkParameters pos [x]      []     = return ()
checkParameters pos [x]      _      = reportError pos NotEnoughArgumentsForDatatype
checkParameters pos (a:args) (p:ps) =
    case a of
      Annot pos' (Var arg) -> do
             when (arg /= p) $ reportError pos' (NonMatchingParameterArgument arg p)
             checkParameters pos args ps
      Annot pos' _         -> do
             reportError pos' (IllFormedArgument p)
checkParameters pos _        []     = reportError pos TooManyArgumentsForDatatype
checkParameters pos []       _      = reportError pos NotEnoughArgumentsForDatatype

--------------------------------------------------------------------------------
makeMuTy :: IDataDecl ->
            [Maybe Ident] ->
            LN.TermPos
makeMuTy d bv = pos @| LN.Pi Nothing idxType (pos @| LN.Set 0)
    where pos     = dataPos d
          idxType = LN.toLocallyNameless (dataIndexType d) bv

-- FIXME: instead of regenerating the code, generate a reference to it
makeMu :: IDataDecl ->
          [Maybe Ident] ->
          LN.TermPos
makeMu d bv = pos @| LN.MuI idxType code
    where pos     = dataPos d
          idxType = LN.toLocallyNameless (dataIndexType d) bv
          code    = makeCode d bv

--------------------------------------------------------------------------------
descType :: IDataDecl -> [Maybe Ident] -> LN.TermPos
descType d bv = pos @| LN.Pi Nothing idxType1 (pos @| LN.App (pos @| LN.IDesc) idxType2)
    where pos      = dataPos d
          idxType1 = LN.toLocallyNameless (dataIndexType d) bv
          idxType2 = LN.toLocallyNameless (dataIndexType d) (Nothing:bv)

--------------------------------------------------------------------------------
-- generate the big sum type to name the constructors
namesSumType :: Span -> [IConstructor] -> LN.TermPos
namesSumType pos []     = pos @| LN.Empty
namesSumType pos [x]    = pos @| LN.Unit
namesSumType pos (x:xs) = pos @| LN.Sum (pos @| LN.Unit) (namesSumType pos xs)

--------------------------------------------------------------------------------
makeCode :: IDataDecl ->
            [Maybe Ident] ->
            LN.TermPos
makeCode d bv = pos @| LN.Lam "i" (pos @| LN.IDesc_Sg namesTy body)
    where
      pos     = dataPos d
      namesTy = namesSumType pos (dataConstructors d)
      body    = pos @| LN.Lam "d" (codeBody d (Nothing:Nothing:bv) 1 (dataConstructors d))

-- expects that the bound variables include the parameters, the index
-- variable and the discriminator at position 0
codeBody :: IDataDecl ->
            [Maybe Ident] ->
            Int ->
            [IConstructor] ->
            LN.TermPos
codeBody d bv idxVar []       =
    -- Special case when we have no constructors
    pos @| LN.App (pos @| LN.App (pos @| LN.ElimEmpty) descType)
                  (pos @| LN.Bound 0)
    where
      pos      = dataPos d
      descType = pos @| LN.App (pos @| LN.IDesc) idxType
      idxType  = LN.toLocallyNameless (dataIndexType d) bv
codeBody d bv idxVar [constr] =
    consCode d bits bv idxVar
    where
      IConstructor p nm bits = constr
codeBody d bv idxVar (constr:constrs) =
    p @| LN.Case discrimVar "x" resultType "a" thisCase "b" otherCases
    where
      IConstructor p nm bits = constr

      discrimVar = p @| LN.Bound 0
      idxType    = LN.toLocallyNameless (dataIndexType d) (Nothing:bv)
      resultType = p @| LN.App (p @| LN.IDesc) idxType
      thisCase   = consCode d bits (Nothing:bv) (idxVar+1)
      otherCases = codeBody d (Nothing:bv) (idxVar+1) constrs

--------------------------------------------------------------------------------
makeConstructors :: IDataDecl ->
                    (LN.TermPos -> LN.TermPos) ->
                    [IConstructor] ->
                    DeclCheckM ()
makeConstructors d consNameCode []               = do
  return ()
makeConstructors d consNameCode [constr]         = do
  let nameCode = consNameCode (consPos constr @| LN.UnitI)
  makeConstructor d nameCode constr
makeConstructors d consNameCode (constr:constrs) = do
  let nameCode = consNameCode (consPos constr @| LN.Inl (consPos constr @| LN.UnitI))
  makeConstructor d nameCode constr 
  makeConstructors d (consNameCode . (\x -> consPos constr @| LN.Inr x)) constrs

--------------------------------------------------------------------------------
paramsType :: [DataParameter] ->
              [Maybe Ident] ->
              ([Maybe Ident] -> LN.TermPos) ->
              LN.TermPos
paramsType []             bv tm = tm bv
paramsType (param:params) bv tm = pos @| LN.Pi (Just nm) tyDom tyCod
    where DataParameter pos nm ty = param
          tyDom = LN.toLocallyNameless ty bv
          tyCod = paramsType params (Just nm:bv) tm

paramsLambda :: [DataParameter] ->
                [Maybe Ident] ->
                ([Maybe Ident] -> LN.TermPos) ->
                LN.TermPos
paramsLambda []             bv tm = tm bv
paramsLambda (param:params) bv tm = pos @| LN.Lam nm tmCod
    where DataParameter pos nm ty = param
          tmCod = paramsLambda params (Just nm:bv) tm

--------------------------------------------------------------------------------
makeConstructor :: IDataDecl ->
                   LN.TermPos ->
                   IConstructor ->
                   DeclCheckM ()
makeConstructor d nameCode constr = do
  let IConstructor p nm xs = constr
      typ = paramsType   (dataParameters d) [] (consType xs)
      trm = paramsLambda (dataParameters d) [] (const $ consTerm nameCode xs)
  checkInternalDefinition p nm typ (Just trm)

--------------------------------------------------------------------------------
consTerm :: LN.TermPos
         -> IConstructorBitsPos
         -> LN.TermPos
consTerm consNameCode constr = lambdas constr 0
    where
      lambdas (Annot p (ConsPi nm t bits)) bv = p @| LN.Lam nm (lambdas bits (bv+1))
      lambdas (Annot p (ConsArr t bits))   bv = p @| LN.Lam "x" (lambdas bits (bv+1))
      lambdas (Annot p (ConsEnd _ _))      bv = p @| LN.Construct (tuple p bv)

      tuple p bv = p @| LN.Pair consNameCode (term constr bv)

      term (Annot p (ConsPi _ _ bits)) bv = p @| LN.Pair (p @| LN.Bound (bv-1)) (term bits (bv-1))
      term (Annot p (ConsArr _ bits))  bv = p @| LN.Pair (p @| LN.Bound (bv-1)) (term bits (bv-1))
      term (Annot p (ConsEnd _ _))     bv = p @| LN.Refl

--------------------------------------------------------------------------------
-- Given a display-level constructor description and a list of binding
-- names, generate the locally-nameless type of the constructor.
consType :: IConstructorBitsPos
         -> [Maybe Ident]
         -> LN.TermPos
consType (Annot p (ConsPi nm t bits)) bv = p @| LN.Pi (Just nm) tyDom tyBits
    where tyBits = consType bits (Just nm:bv)
          tyDom  = LN.toLocallyNameless t bv
consType (Annot p (ConsArr t bits))   bv = p @| LN.Pi Nothing tyDom tyBits
    where tyBits = consType bits (Nothing:bv)
          tyDom  = LN.toLocallyNameless t bv
consType (Annot p (ConsEnd nm ts))    bv = foldl doArg hd ts
    where hd          = p @| LN.Free nm
          doArg t arg = p @| LN.App t (LN.toLocallyNameless arg bv)

--------------------------------------------------------------------------------
-- Given the full datatype declaration, the display-level constructor
-- description, a binding environment, and the de Bruijn index of the
-- index variable, generate the locallynameless term for the
-- description of this constructor.
consCode :: IDataDecl
         -> IConstructorBitsPos
         -> [Maybe Ident]
         -> Int
         -> LN.TermPos
consCode d (Annot p (ConsPi nm t bits)) bv idxVar = p @| LN.IDesc_Sg t' (p @| LN.Lam nm code)
    where t'   = LN.toLocallyNameless t bv
          code = consCode d bits (Just nm:bv) (idxVar+1)

consCode d (Annot p (ConsArr t bits))   bv idxVar = p @| LN.Desc_Prod codeDom code
    where t'      = LN.toLocallyNameless t bv
          p'      = makeSpan t' t'
          codeDom = (p' @| LN.Desc_K t') `fromMaybe` (extractRecursiveCall d t')
          code    = consCode d bits bv idxVar

consCode d (Annot p (ConsEnd nm ts))    bv idxVar = p @| LN.Desc_K (p @| LN.Eq idxVal idx)
    where args   = reverse ts
          idx    = p @| LN.Bound idxVar
          idxVal = LN.toLocallyNameless (head args) bv -- FIXME: handle types with no index

--------------------------------------------------------------------------------
-- Extracts a recursive call to the datatype currently being defined
extractRecursiveCall :: IDataDecl
                     -> LN.TermPos
                     -> Maybe LN.TermPos
extractRecursiveCall d t = loop t
    where
      loop (Annot p (LN.Pi nm t t')) =
          do code <- loop t'
             return (p @| LN.IDesc_Pi t (p @| LN.Lam (fromMaybe "x" nm) code))
      loop t =
          do (p, nm, args) <- extractApplication t
             -- we only care about applications with the right name
             -- FIXME: handle mutually inductive types
             guard (nm == dataName d)
             -- FIXME: check the parameters against the names
             let idxVal = head args -- FIXME: handle non-indexed data
             return (p @| LN.IDesc_Id idxVal)

-- if the given term is of the form
--     nm @ t1 @ ... @ t2
-- then return the position of nm, nm, and the ti in reverse order
-- otherwise return 'Nothing'
extractApplication :: LN.TermPos
                   -> Maybe (Span, Ident, [LN.TermPos])
extractApplication t = loop t
    where
      loop (Annot p (LN.Free nm))  = return (p, nm, [])
      loop (Annot p (LN.App t t')) = do (p, nm, l) <- loop t
                                        return (p, nm, t':l)
      loop _                       = Nothing
