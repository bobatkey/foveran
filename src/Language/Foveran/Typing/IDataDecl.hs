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
import           Text.Position (Span (..), initPos)

--------------------------------------------------------------------------------
pDefault = Span initPos initPos -- FIXME: get these from the IConstructorBits

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
  checkInternalDefinition pDefault codeName codeType (Just code)

  -- Generate the type itself
  let typ = paramsType   (dataParameters d) [] (makeMuTy d)
      trm = paramsLambda (dataParameters d) [] (makeMu d)
  checkInternalDefinition pDefault (dataName d) typ (Just trm)

  -- Generate the functions for each of the constructors
  makeConstructors d id (dataConstructors d)

--------------------------------------------------------------------------------
checkParameterName :: (Ident, TermPos) ->
                      StateT (S.Set Ident) DeclCheckM ()
checkParameterName (paramName, _) = do
  usedNames <- get
  when (paramName `S.member` usedNames) $ lift $ reportError pDefault (DuplicateParameterName paramName)
  put (S.insert paramName usedNames)

--------------------------------------------------------------------------------
checkConstructor :: IDataDecl ->
                    IConstructor ->
                    StateT (S.Set Ident) DeclCheckM ()
checkConstructor d (IConstructor nm components) = do
  usedNames <- get
  when (nm `S.member` usedNames) $ lift $ reportError pDefault (DuplicateConstructorName nm)
  lift $ checkConstructorsBits d components
  put (S.insert nm usedNames)

checkConstructorsBits :: IDataDecl ->
                         IConstructorBits ->
                         DeclCheckM ()
checkConstructorsBits d (ConsPi nm t bits) = do
  when (nm == dataName d) $ reportError pDefault ShadowingDatatypeName
  when (nm `elem` (map fst $ dataParameters d)) $ reportError pDefault ShadowingParameterName
  checkConstructorsBits d bits
checkConstructorsBits d (ConsArr t bits) = do
  -- FIXME: extract the recursive call if it exists and check to see
  -- whether it properly uses the parameter names
  checkConstructorsBits d bits
checkConstructorsBits d (ConsEnd nm ts) = do
  unless (nm == dataName d) $ reportError pDefault (ConstructorTypesMustEndWithNameOfDatatype nm (dataName d))
  checkParameters ts (map fst $ dataParameters d)

checkParameters :: [TermPos] -> [Ident] -> DeclCheckM ()
checkParameters [x]      []     = return ()
checkParameters [x]      _      = reportError pDefault NotEnoughArgumentsForDatatype
checkParameters (a:args) (p:ps) =
    case a of
      Annot pos (Var arg) -> do
             when (arg /= p) $ reportError pos (NonMatchingParameterArgument arg p)
             checkParameters args ps
      Annot pos _         -> do
             reportError pos (IllFormedArgument p)
checkParameters _        []     = reportError pDefault TooManyArgumentsForDatatype
checkParameters []       _      = reportError pDefault NotEnoughArgumentsForDatatype

--------------------------------------------------------------------------------
makeMuTy :: IDataDecl ->
            [Maybe Ident] ->
            LN.TermPos
makeMuTy d bv = pDefault @| LN.Pi Nothing idxType (pDefault @| LN.Set 0)
    where idxType = LN.toLocallyNameless (dataIndexType d) bv

-- FIXME: instead of regenerating the code, generate a reference to it
makeMu :: IDataDecl ->
          [Maybe Ident] ->
          LN.TermPos
makeMu d bv = pDefault @| LN.MuI idxType code
    where idxType = LN.toLocallyNameless (dataIndexType d) bv
          code    = makeCode d bv

--------------------------------------------------------------------------------
descType :: IDataDecl -> [Maybe Ident] -> LN.TermPos
descType d bv = pDefault @| LN.Pi Nothing idxType1 (pDefault @| LN.App (pDefault @| LN.IDesc) idxType2)
    where idxType1 = LN.toLocallyNameless (dataIndexType d) bv
          idxType2 = LN.toLocallyNameless (dataIndexType d) (Nothing:bv)

--------------------------------------------------------------------------------
-- generate the big sum type to name the constructors
namesSumType :: [IConstructor] -> LN.TermPos
namesSumType []     = pDefault @| LN.Empty
namesSumType [x]    = pDefault @| LN.Unit
namesSumType (x:xs) = pDefault @| LN.Sum (pDefault @| LN.Unit) (namesSumType xs)

--------------------------------------------------------------------------------
makeCode :: IDataDecl ->
            [Maybe Ident] ->
            LN.TermPos
makeCode d bv = pDefault @| LN.Lam "i" (pDefault @| LN.IDesc_Sg namesTy body)
    where
      namesTy = namesSumType (dataConstructors d)
      body    = pDefault @| LN.Lam "d" (codeBody d (Nothing:Nothing:bv) 1 (dataConstructors d))

-- expects that the bound variables include the parameters, the index
-- variable and the discriminator at position 0
codeBody :: IDataDecl ->
            [Maybe Ident] ->
            Int ->
            [IConstructor] ->
            LN.TermPos
codeBody d bv idxVar []       =
    pDefault @| LN.App (pDefault @| LN.App (pDefault @| LN.ElimEmpty) descType)
                       (pDefault @| LN.Bound 0)
    where
      descType = pDefault @| LN.App (pDefault @| LN.IDesc) idxType
      idxType  = LN.toLocallyNameless (dataIndexType d) bv
codeBody d bv idxVar [constr] =
    consCode d bits bv idxVar
    where
      IConstructor nm bits = constr
codeBody d bv idxVar (constr:constrs) =
    pDefault @| LN.Case discrimVar "x" resultType "a" thisCase "b" otherCases
    where
      IConstructor nm bits = constr

      discrimVar = pDefault @| LN.Bound 0
      idxType    = LN.toLocallyNameless (dataIndexType d) (Nothing:bv)
      resultType = pDefault @| LN.App (pDefault @| LN.IDesc) idxType
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
  let nameCode = consNameCode (pDefault @| LN.UnitI)
  makeConstructor d nameCode constr
makeConstructors d consNameCode (constr:constrs) = do
  let nameCode = consNameCode (pDefault @| LN.Inl (pDefault @| LN.UnitI))
  makeConstructor d nameCode constr 
  makeConstructors d (consNameCode . (\x -> pDefault @| LN.Inr x)) constrs

--------------------------------------------------------------------------------
paramsType :: [(Ident,TermPos)] ->
              [Maybe Ident] ->
              ([Maybe Ident] -> LN.TermPos) ->
              LN.TermPos
paramsType []           bv tm = tm bv
paramsType ((nm,ty):xs) bv tm = pDefault @| LN.Pi (Just nm) tyDom tyCod
    where tyDom = LN.toLocallyNameless ty bv
          tyCod = paramsType xs (Just nm:bv) tm

paramsLambda :: [(Ident,TermPos)] ->
                [Maybe Ident] ->
                ([Maybe Ident] -> LN.TermPos) ->
                LN.TermPos
paramsLambda []           bv tm = tm bv
paramsLambda ((nm,ty):xs) bv tm = pDefault @| LN.Lam nm tmCod
    where tmCod = paramsLambda xs (Just nm:bv) tm

--------------------------------------------------------------------------------
makeConstructor :: IDataDecl ->
                   LN.TermPos ->
                   IConstructor ->
                   DeclCheckM ()
makeConstructor d nameCode constr = do
  let IConstructor nm xs = constr
      typ = paramsType   (dataParameters d) [] (consType xs)
      trm = paramsLambda (dataParameters d) [] (const $ consTerm nameCode xs)
  checkInternalDefinition pDefault nm typ (Just trm)

--------------------------------------------------------------------------------
consTerm :: LN.TermPos
         -> IConstructorBits
         -> LN.TermPos
consTerm consNameCode constr = lambdas constr 0
    where
      lambdas (ConsPi nm t bits) bv = pDefault @| LN.Lam nm (lambdas bits (bv+1))
      lambdas (ConsArr t bits)   bv = pDefault @| LN.Lam "x" (lambdas bits (bv+1))
      lambdas (ConsEnd _ _)      bv = pDefault @| LN.Construct (tuple bv)

      tuple bv = pDefault @| LN.Pair consNameCode (term constr bv)

      term (ConsPi _ _ bits) bv = pDefault @| LN.Pair (pDefault @| LN.Bound (bv-1)) (term bits (bv-1))
      term (ConsArr _ bits)  bv = pDefault @| LN.Pair (pDefault @| LN.Bound (bv-1)) (term bits (bv-1))
      term (ConsEnd _ _)     bv = pDefault @| LN.Refl

--------------------------------------------------------------------------------
-- Given a display-level constructor description and a list of binding
-- names, generate the locally-nameless type of the constructor.
consType :: IConstructorBits
         -> [Maybe Ident]
         -> LN.TermPos
consType (ConsPi nm t bits) bv = pDefault @| LN.Pi (Just nm) tyDom tyBits
    where tyBits = consType bits (Just nm:bv)
          tyDom  = LN.toLocallyNameless t bv
consType (ConsArr t bits)   bv = pDefault @| LN.Pi Nothing tyDom tyBits
    where tyBits = consType bits (Nothing:bv)
          tyDom  = LN.toLocallyNameless t bv
consType (ConsEnd nm ts)    bv = foldl doArg hd ts
    where hd          = pDefault @| LN.Free nm
          doArg t arg = pDefault @| LN.App t (LN.toLocallyNameless arg bv)

--------------------------------------------------------------------------------
-- Given the full datatype declaration, the display-level constructor
-- description, a binding environment, and the de Bruijn index of the
-- index variable, generate the locallynameless term for the
-- description of this constructor.
consCode :: IDataDecl
         -> IConstructorBits
         -> [Maybe Ident]
         -> Int
         -> LN.TermPos
consCode d (ConsPi nm t bits) bv idxVar = pDefault @| LN.IDesc_Sg t' (pDefault @| LN.Lam nm code)
    where t'   = LN.toLocallyNameless t bv
          code = consCode d bits (Just nm:bv) (idxVar+1)

consCode d (ConsArr t bits)   bv idxVar = pDefault @| LN.Desc_Prod codeDom code
    where t'      = LN.toLocallyNameless t bv
          codeDom = (pDefault @| LN.Desc_K t') `fromMaybe` (extractRecursiveCall d t')
          code    = consCode d bits bv idxVar

consCode d (ConsEnd nm ts)    bv idxVar = pDefault @| LN.Desc_K (pDefault @| LN.Eq idxVal idx)
    where args   = reverse ts
          idx    = pDefault @| LN.Bound idxVar
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
