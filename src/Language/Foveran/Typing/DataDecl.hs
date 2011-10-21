{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.DataDecl
    ( checkDatatype )
    where

import Data.Functor
import Data.Monoid
import Data.Rec
import Language.Foveran.Syntax.Display
import Language.Foveran.Typing.DeclCheckMonad
import Language.Foveran.Typing.Definition (processDefinition)
import Text.Position (Span)
import qualified Data.Text as T

checkDatatype :: Datatype -> DeclCheckM ()
checkDatatype d =
    do processDefinition (genDesc d)
       processDefinition (genDatatypeCarrier d)
       mapM_ processDefinition (genConstructors d)

-- step 1: create a description for the given declaration
--  step 1a: create a type for the description of the given declaration
--  step 1b: create the description itself

unitDesc p = Annot p $ Desc_K (Annot p $ Unit)
zeroDesc p = Annot p $ Desc_K (Annot p $ Empty)
plusDesc p x y = Annot p $ Desc_Sum x y
timesDesc p x y = Annot p $ Desc_Prod x y

paramsType :: Span -> [(Ident,TermPos)] -> TermPos -> TermPos
paramsType p []               t = t
paramsType p ((nm,ty):params) t = Annot p $ Pi [([nm], ty)] (paramsType p params t)

paramsLam :: Span -> [(Ident,TermPos)] -> TermPos -> TermPos
paramsLam p params t = Annot p $ Lam (fst <$> params) t

data ConsElem = Recursive
              | Fixed     TermPos

processConstructorArgs :: Ident -> [TermPos] -> [ConsElem]
processConstructorArgs nm = map processConstructorArg
    where
      processConstructorArg (Annot _ (Var nm'))
          | nm == nm' = Recursive
      processConstructorArg tm = Fixed tm

genDesc :: Datatype -> Definition
genDesc (Datatype p nm params constructors) =
    Definition p descNm descTy descNm descTm
    where
      descTy = paramsType p params (Annot p Desc)
    
      descNm = nm `mappend` "Desc"
               
      descTm = case constructors of
                 [] -> paramsLam p params (zeroDesc p)
                 l  -> paramsLam p params $ foldr1 (plusDesc p) $ map constructorDesc l

      constructorDesc (Constructor _ [])    = unitDesc p
      constructorDesc (Constructor _ elems) = foldr1 (timesDesc p) $ map elemDesc $ processConstructorArgs nm elems
      
      elemDesc Recursive  = Annot p Desc_Id
      elemDesc (Fixed tm) = Annot p (Desc_K tm)

genDatatypeCarrier :: Datatype -> Definition
genDatatypeCarrier (Datatype p nm params constructors) =
    Definition p nm ty nm tm
    where
      nmDesc = nm `mappend` "Desc"
      
      ty = paramsType p params (Annot p $ Set 0)

      tm = paramsLam p params (Annot p $ Mu (Annot p $ App (Annot p $ Var nmDesc) (map (\(nm,_) -> Annot p $ Var nm) params)))

makePair p x y = Annot p $ Pair x y

genConstructors :: Datatype -> [Definition]
genConstructors (Datatype p nm params constructors) = genConsLoop id constructors
    where
      nmDesc = nm `mappend` "Desc"
      descTm = Annot p $ App (Annot p $ Var nmDesc) paramVars

      genConsLoop f []     = []
      genConsLoop f [x]    = [genCons f x]
      genConsLoop f (x:xs) = genCons (\x -> f (Annot p $ Inl x)) x : genConsLoop (\x -> f (Annot p $ Inr x)) xs

      genCons inject (Constructor consNm elems) =
        let elems' = processConstructorArgs nm elems
        in
          Definition p consNm (consType elems') consNm (consTerm inject elems')

      paramVars = map (\(nm,_) -> Annot p $ Var nm) params
      
      selfTy = Annot p $ App (Annot p $ Var nm) paramVars

      consType elems = paramsType p params (foldr elemType selfTy elems)
      
      elemType Recursive  t = Annot p $ Pi [([],selfTy)] t
      elemType (Fixed ty) t = Annot p $ Pi [([],ty)] t

      -- FIXME: be cleverer about freshness;
      -- should probably be using the locally nameless representation
      elemVarNms elems = map (\(i,_) -> "__x" `mappend` (T.pack $ show i)) $ zip [1..] elems

      consLam []    t = t
      consLam elems t = Annot p $ Lam (elemVarNms elems) t
      consArg []      = Annot p $ UnitI
      consArg elems   = foldr1 (makePair p) $ map (Annot p . Var) $ elemVarNms elems 

      consTerm inject elems =
        paramsLam p params $ consLam elems $ Annot p (Construct (inject $ consArg elems))
