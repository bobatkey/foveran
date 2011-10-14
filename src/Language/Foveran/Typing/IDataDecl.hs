{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.IDataDecl
    ( checkIDataDecl )
    where

import Control.Monad (unless, guard)
import Data.Maybe (fromMaybe, fromJust) -- FIXME: remove fromJust
import Data.Rec (AnnotRec (Annot))
import Language.Foveran.Typing.DeclCheckMonad
import Language.Foveran.Syntax.Display
import Language.Foveran.Syntax.Identifier ((<+>))
import qualified Language.Foveran.Syntax.LocallyNameless as LN
import Language.Foveran.Parsing.PrettyPrinter (ppIDataDecl)
import Text.Position (Span (..), initPos)
import Text.PrettyPrint (render)

--------------------------------------------------------------------------------
pDefault = Span initPos initPos -- FIXME: get these from the IConstructorBits

(@|) p t = Annot p t

--------------------------------------------------------------------------------
checkIDataDecl :: IDataDecl -> DeclCheckM Span ()
checkIDataDecl d = do
  -- liftIO $ putStrLn (render $ ppIDataDecl d)

  -- FIXME: check all the constructors and stuff for shadowing and incorrect names

  let codeName = dataName d <+> ":code"
      codeType = paramsType   (dataParameters d) [] (descType d)
      code     = paramsLambda (dataParameters d) [] (makeCode d)
  checkInternalDefinition pDefault codeName codeType code

  let typ = paramsType   (dataParameters d) [] (makeMuTy d)
      trm = paramsLambda (dataParameters d) [] (makeMu d)
  checkInternalDefinition pDefault (dataName d) typ trm

  makeConstructors d id (dataConstructors d)

--------------------------------------------------------------------------------
-- FIXME: instead of regenerating the code, generate a call back to it
makeMuTy d bv = pDefault @| LN.Pi Nothing idxType (pDefault @| LN.Set 0)
    where idxType = LN.toLocallyNameless (dataIndexType d) bv

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
makeCode d bv = pDefault @| LN.Lam "i" (pDefault @| LN.IDesc_Sg namesTy body)
    where
      namesTy = namesSumType (dataConstructors d)
      body    = pDefault @| LN.Lam "d" (codeBody d (Nothing:Nothing:bv) 1 (dataConstructors d))

-- expects that the bound variables include the parameters, the index
-- variable and the discriminator at position 0
codeBody d bv idxVar []       =
    pDefault @| LN.App (pDefault @| LN.App (pDefault @| LN.ElimEmpty) descType)
                       (pDefault @| LN.Bound 0)
    where
      descType = pDefault @| LN.App (pDefault @| LN.IDesc) idxType
      idxType  = LN.toLocallyNameless (dataIndexType d) bv
codeBody d bv idxVar [constr] =
    fromJust $ consCode d bits bv idxVar
    where
      IConstructor nm bits = constr
codeBody d bv idxVar (constr:constrs) =
    pDefault @| LN.Case discrimVar "x" resultType "a" thisCase "b" otherCases
    where
      IConstructor nm bits = constr

      discrimVar = pDefault @| LN.Bound 0
      resultType = pDefault @| LN.App (pDefault @| LN.IDesc) (LN.toLocallyNameless (dataIndexType d) (Nothing:bv))
      thisCase   = fromJust $ consCode d bits (Nothing:bv) (idxVar+1)
      otherCases = codeBody d (Nothing:bv) (idxVar+1) constrs

--------------------------------------------------------------------------------
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
paramsType :: [(Ident,TermPos)] -> [Maybe Ident] -> ([Maybe Ident] -> LN.TermPos) -> LN.TermPos
paramsType []           bv tm = tm bv
paramsType ((nm,ty):xs) bv tm = pDefault @| LN.Pi (Just nm) tyDom tyCod
    where tyDom = LN.toLocallyNameless ty bv
          tyCod = paramsType xs (Just nm:bv) tm

paramsLambda :: [(Ident,TermPos)] -> [Maybe Ident] -> ([Maybe Ident] -> LN.TermPos) -> LN.TermPos
paramsLambda []           bv tm = tm bv
paramsLambda ((nm,ty):xs) bv tm = pDefault @| LN.Lam nm tmCod
    where tmCod = paramsLambda xs (Just nm:bv) tm

--------------------------------------------------------------------------------
makeConstructor d nameCode constr = do
  let IConstructor nm xs = constr
      typ = paramsType   (dataParameters d) [] (consType xs)
      trm = paramsLambda (dataParameters d) [] (const $ consTerm nameCode xs)
  checkInternalDefinition pDefault nm typ trm

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
consCode :: Monad m =>
            IDataDecl
         -> IConstructorBits
         -> [Maybe Ident]
         -> Int
         -> m (AnnotRec Span LN.TermCon)
consCode d (ConsPi nm t bits) bv idxVar = do
  -- FIXME: check for shadowing of the name of the datatype, and of
  -- the parameters
  code <- consCode d bits (Just nm:bv) (idxVar+1)
  let t' = LN.toLocallyNameless t bv
  return (pDefault @| LN.IDesc_Sg t' (pDefault @| LN.Lam nm code))

consCode d (ConsArr t bits)   bv idxVar = do
  let t'         = LN.toLocallyNameless t bv
  let codeDom    = (pDefault @| LN.Desc_K t') `fromMaybe` (extractRecursiveCall d t')
  code <- consCode d bits bv idxVar
  return (pDefault @| LN.Desc_Prod codeDom code)

consCode d (ConsEnd nm ts)    bv idxVar = do
  unless (nm == dataName d) $ fail "wrong name" -- FIXME: proper error
  let args = reverse ts
  -- FIXME: check all the parameters against the names
  let idx    = pDefault @| LN.Bound idxVar
      idxVal = LN.toLocallyNameless (head args) bv -- FIXME: handle types with no index
  return (pDefault @| LN.Desc_K (pDefault @| LN.Eq idxVal idx))

--------------------------------------------------------------------------------
-- Extracts a recursive call to the datatype currently being defined
extractRecursiveCall :: IDataDecl
                     -> AnnotRec a LN.TermCon
                     -> Maybe (AnnotRec a LN.TermCon)
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
extractApplication :: AnnotRec t LN.TermCon
                   -> Maybe (t, Ident, [AnnotRec t LN.TermCon])
extractApplication t = do
  (p, nm, args) <- loop t
  return (p, nm, args)
    where
      loop (Annot p (LN.Free nm))  = 
          return (p, nm, [])
      loop (Annot p (LN.App t t')) =
          do (p, nm, l) <- loop t
             return (p, nm, t':l)
      loop _ = Nothing
