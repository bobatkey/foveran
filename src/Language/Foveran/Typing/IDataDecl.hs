{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.IDataDecl
    ( processIDataDecl )
    where

import qualified Data.Set as S
import           Control.Monad (unless, guard, when, forM_, forM)
import           Control.Monad.State (StateT, evalStateT, gets, lift, modify)
import           Data.Maybe (fromMaybe, isJust)
import           Data.Rec (AnnotRec (Annot))
import           Language.Foveran.Typing.DeclCheckMonad
import           Language.Foveran.Typing.Errors (DataDeclError (..))
import           Language.Foveran.Syntax.Display
import           Language.Foveran.Syntax.Identifier ((<+>))
import qualified Language.Foveran.Syntax.LocallyNameless as LN
import           Text.Position (Span (..), makeSpan)

--------------------------------------------------------------------------------
evalStateTWith :: Monad m => s -> StateT s m a -> m a
evalStateTWith = flip evalStateT

(@|) p t = Annot p t

--------------------------------------------------------------------------------
processIDataDecl :: IDataDecl -> DeclCheckM ()
processIDataDecl d = do
  evalStateTWith S.empty $ do
    forM_ (dataParameters d) checkParameterName

  -- Check the constructors for duplicate names, shadowing and
  -- correctness of parameter names. Does not check for any type
  -- correctness.
  constructors <- evalStateTWith S.empty $ do
    forM (dataConstructors d) (checkConstructor d)

  -- Generate the description of this datatype
  let codeName = dataName d <+> ":code"
      codeTyp  = paramsType   (dataParameters d) (codeType d) []
      code     = paramsLambda (dataParameters d) (makeCode d constructors) []
  checkDefinition (dataPos d) codeName codeTyp (Just code)

  -- Generate the type itself
  let typ = paramsType   (dataParameters d) (makeMuTy d) []
      trm = paramsLambda (dataParameters d) (makeMu d) []
  checkDefinition (dataPos d) (dataName d) typ (Just trm)

--------------------------------------------------------------------------------
checkParameterName :: DataParameter ->
                      StateT (S.Set Ident) DeclCheckM ()
checkParameterName (DataParameter pos paramName _) = do
  nameUsed <- gets (S.member paramName)
  when nameUsed $ do
    lift $ reportDataDeclError pos (DuplicateParameterName paramName)
  modify (S.insert paramName)

--------------------------------------------------------------------------------
-- Intermediate representation of constructors, after the parameter
-- lists have been checked, and recursive references have been
-- discovered.

-- These are still in Display syntax, because we will have to
-- translate them to multiple binding contexts.
data ConstructorArg
    = ConsArg  Span (Maybe Ident) TermPos
    | ConsCall Span (Maybe Ident) [(Pattern, TermPos)] TermPos

data Constructor =
    Constructor { consPos       :: Span
                , consIdent     :: Ident
                , consArgs      :: [ConstructorArg]
                , consResultIdx :: TermPos
                }

--------------------------------------------------------------------------------
checkConstructor :: IDataDecl
                 -> IConstructor
                 -> StateT (S.Set Ident) DeclCheckM Constructor
checkConstructor d (IConstructor pos nm bits) = do
  nameUsed <- gets (S.member nm)
  when nameUsed $ do
    lift $ reportDataDeclError pos (DuplicateConstructorName nm)
  modify (S.insert nm)
  (args, idxTm) <- lift $ checkConstructorBits d bits
  return (Constructor pos nm args idxTm)

checkConstructorBits :: IDataDecl
                     -> IConstructorBitsPos
                     -> DeclCheckM ([ConstructorArg], TermPos)
checkConstructorBits d (Annot p (ConsPi nm t bits)) = do
  when (nm == dataName d) $ reportDataDeclError p ShadowingDatatypeName
  when (nm `elem` (map paramIdent $ dataParameters d)) $ reportDataDeclError p ShadowingParameterName
  (args, idxTm) <- checkConstructorBits d bits
  return (ConsArg p (Just nm) t : args, idxTm)
checkConstructorBits d (Annot p (ConsArr t bits)) = do
  (args, idxTm) <- checkConstructorBits d bits
  case extractRecursiveCall d t of
    Nothing                   ->
        do return (ConsArg p Nothing t : args, idxTm)
    Just (bindings, callArgs) ->
        do callIdxTm <- checkParameters p (isJust (dataIndexType d)) callArgs (map paramIdent $ dataParameters d)
           return (ConsCall p Nothing bindings callIdxTm : args, idxTm)
checkConstructorBits d (Annot p (ConsEnd nm tms)) = do
  when (nm /= dataName d) $ reportDataDeclError p (ConstructorTypesMustEndWithNameOfDatatype nm (dataName d))
  idxTm <- checkParameters p (isJust (dataIndexType d)) tms (map paramIdent $ dataParameters d)
  return ([], idxTm)

checkParameters :: Span      -- ^ The position at which to report any errors
                -> Bool      -- ^ Whether or not we are looking for an index argument at the end
                -> [TermPos] -- ^ The supplied list of arguments
                -> [Ident]   -- ^ The list of declared names of the parameter arguments
                -> DeclCheckM TermPos -- ^ The index argument. Will be UnitI if we are not expecting a user supplied index argument
checkParameters pos False   []       []     = return (pos @| UnitI)
checkParameters pos False   []       (p:ps) = reportDataDeclError pos NotEnoughArgumentsForDatatype
checkParameters pos True    [x]      []     = return x
checkParameters pos True    [x]      (p:ps) = reportDataDeclError pos NotEnoughArgumentsForDatatype
checkParameters pos needIdx _        []     = reportDataDeclError pos TooManyArgumentsForDatatype
checkParameters pos needIdx []       _      = reportDataDeclError pos NotEnoughArgumentsForDatatype
checkParameters pos needIdx (a:args) (p:ps) =
    case a of
      Annot pos' (Var arg) -> do when (arg /= p) $ reportDataDeclError pos' (NonMatchingParameterArgument arg p)
                                 checkParameters pos needIdx args ps
      Annot pos' _         -> do reportDataDeclError pos' (IllFormedArgument p)

extractRecursiveCall :: IDataDecl
                     -> TermPos
                     -> Maybe ([(Pattern, TermPos)], [TermPos])
extractRecursiveCall d t = loop t
    where
      loop (Annot p (Pi bindings t)) =
          do let args = [ (pat, t) | (pats, t) <- bindings
                                   , pat <- case pats of [] -> [PatNull]; nms -> nms]
             (args', tms) <- loop t
             return (args ++ args', tms)
      loop (Annot p (App (Annot p' (Var nm)) tms)) =
          do guard (nm == dataName d)
             return ([], tms)
      loop (Annot p (Var nm)) =
          do guard (nm == dataName d)
             return ([], [])
      loop _ = Nothing

--------------------------------------------------------------------------------
paramsType :: [DataParameter] ->
              ([LN.Binding] -> LN.TermPos) ->
              [LN.Binding] -> LN.TermPos
paramsType []             tm bv = tm bv
paramsType (param:params) tm bv = pos @| LN.Pi (Just nm) tyDom tyCod
    where DataParameter pos nm ty = param
          tyDom = LN.toLocallyNameless ty bv
          tyCod = paramsType params tm (LN.BindVar nm:bv)

paramsLambda :: [DataParameter] ->
                ([LN.Binding] -> LN.TermPos) ->
                [LN.Binding] -> LN.TermPos
paramsLambda []             tm bv = tm bv
paramsLambda (param:params) tm bv = pos @| LN.Lam nm tmCod
    where DataParameter pos nm ty = param
          tmCod = paramsLambda params tm (LN.BindVar nm:bv)

-- assumes that the list of parameters is bound with the correct names
paramsApp :: [DataParameter]
          -> LN.TermPos
          -> [LN.Binding] -> LN.TermPos
paramsApp []             tm bv = tm
paramsApp (param:params) tm bv =
    paramsApp params (pos @| LN.App tm (LN.toLocallyNameless (pos @| Var nm) bv)) bv
    where DataParameter pos nm ty = param

--------------------------------------------------------------------------------
makeMuTy :: IDataDecl
         -> [LN.Binding]
         -> LN.TermPos
makeMuTy d bv =
    case dataIndexType d of
      Nothing    -> pos @| LN.Set 0
      Just idxTy -> pos @| LN.Pi Nothing (LN.toLocallyNameless idxTy bv) (pos @| LN.Set 0)
    where pos     = dataPos d

-- assumes that the parameter names are bound
makeMu :: IDataDecl
       -> [LN.Binding]
       -> LN.TermPos
makeMu d bv =
    case dataIndexType d of
      Nothing    -> pos @| LN.App (pos @| LN.MuI (pos @| LN.Unit Nothing) code) (pos @| LN.UnitI)
      Just idxTy -> pos @| LN.MuI (LN.toLocallyNameless idxTy bv) code
    where pos     = dataPos d
          codeVar = pos @| LN.Free (dataName d <+> ":code") LN.IsGlobal
          code    = paramsApp (dataParameters d) codeVar bv

--------------------------------------------------------------------------------
-- Generates the type of the code for the datatype, given a binding
-- environment for the parameters
codeType :: IDataDecl
         -> [LN.Binding]
         -> LN.TermPos
codeType d bv =
    pos @| LN.Pi Nothing (idxType bv)
           (pos @| LN.App (pos @| LN.IDesc) (idxType (LN.BindNull:bv)))
    where
      pos     = dataPos d
      idxType = case dataIndexType d of
                  Nothing    -> \bv -> pos @| LN.Unit Nothing
                  Just idxTy -> LN.toLocallyNameless idxTy

--------------------------------------------------------------------------------
-- generate the big sum type to name the constructors
namesSumType :: Span -> [Constructor] -> LN.TermPos
namesSumType pos []     = pos @| LN.Empty
namesSumType pos [x]    = pos @| LN.Unit (Just $ consIdent x)
namesSumType pos (x:xs) = pos @| LN.Sum (pos @| LN.Unit (Just $ consIdent x)) (namesSumType pos xs)

--------------------------------------------------------------------------------
makeCode :: IDataDecl
         -> [Constructor]
         -> [LN.Binding]
         -> LN.TermPos
makeCode d constrs bv = pos @| LN.Lam "i" (pos @| LN.IDesc_Sg namesTy body)
    where
      pos     = dataPos d
      namesTy = namesSumType pos constrs
      body    = pos @| LN.Lam "d" (codeBody d (LN.BindNull:LN.BindNull:bv) 1 constrs)

-- expects that the bound variables include the parameters, the index
-- variable and the discriminator at position 0
codeBody :: IDataDecl
         -> [LN.Binding]
         -> Int
         -> [Constructor]
         -> LN.TermPos
codeBody d bv idxVar []       =
    -- Special case when we have no constructors
    pos @| LN.ElimEmpty (pos @| LN.Bound 0) Nothing
    where
      pos      = dataPos d
codeBody d bv idxVar [constr] =
    consCode d constr bv idxVar
codeBody d bv idxVar (constr:constrs) =
    p @| LN.Case discrimVar (Just ("x", resultType)) "a" thisCase "b" otherCases
    where
      p          = dataPos d

      discrimVar = p @| LN.Bound 0
      idxType    = case dataIndexType d of
                     Nothing    -> p @| LN.Unit Nothing
                     Just idxTy -> LN.toLocallyNameless idxTy (LN.BindNull:bv)
      resultType = p @| LN.App (p @| LN.IDesc) idxType
      thisCase   = consCode d constr (LN.BindNull:bv) (idxVar+1)
      otherCases = codeBody d (LN.BindNull:bv) (idxVar+1) constrs

--------------------------------------------------------------------------------
consCode :: IDataDecl
         -> Constructor
         -> [LN.Binding]
         -> Int
         -> LN.TermPos
consCode d constr =
    foldr (consBitCode d) (consEndCode d (consResultIdx constr)) $ consArgs constr

consEndCode :: IDataDecl
            -> TermPos
            -> [LN.Binding] -> Int -> LN.TermPos
consEndCode d idxTm bv idxVar =
    p @| LN.Desc_K (p @| LN.Eq idxTm' idx)
    where
      p      = dataPos d -- FIXME: this location ought to be the location of the ConsEnd bit
      idx    = p @| LN.Bound idxVar
      idxTy  = case dataIndexType d of
                 Nothing   -> p @| LN.Unit Nothing
                 Just ty   -> LN.toLocallyNameless ty bv
      idxTm' = p @| LN.TypeAscrip (LN.toLocallyNameless idxTm bv) idxTy

consBitCode :: IDataDecl
            -> ConstructorArg
            -> ([LN.Binding] -> Int -> LN.TermPos)
            -> [LN.Binding] -> Int -> LN.TermPos
consBitCode d (ConsArg pos maybeNm t) rest bv idxVar =
    pos @| LN.IDesc_Sg t' (pos @| LN.Lam nm code)
    where
      nm   = fromMaybe "x" maybeNm
      pat  = case maybeNm of Nothing -> LN.BindNull; Just nm -> LN.BindVar nm
      t'   = LN.toLocallyNameless t bv
      code = rest (pat:bv) (idxVar+1)
consBitCode d (ConsCall pos maybeNm hyps idxTm) rest bv idxVar =
    pos @| LN.Desc_Prod codeCall code
    where
      code     = rest bv idxVar
      codeCall = foldr makeHyp makeCall hyps bv

      makeCall bv =
          let idxTm' = LN.toLocallyNameless idxTm bv
          -- FIXME: get the position from idxTm'
          in pos @| LN.IDesc_Id idxTm'

      makeHyp (pat, t) rest bv =
          let t'   = LN.toLocallyNameless t bv
              code = rest (LN.bindingOfPattern pat:bv)
          -- FIXME: get the position from t'
          in pos @| LN.IDesc_Pi t' (pos @| LN.Lam "x" code)
