{-# LANGUAGE TypeSynonymInstances, DeriveFunctor, FlexibleInstances #-}

module Language.Foveran.Syntax.Checked
    ( Ident
    , Term
    , TermCon (..)
    , tmApp
    , tmFree
    , tmBound
    , tmFst
    , tmSnd
    , vbound
      
    , bindFree
    , generalise
    , toDisplaySyntax
    )
    where

import           Control.Applicative
import           Data.Rec
import           Data.List (elemIndex)
import qualified Language.Foveran.Syntax.Display as DS
import           Language.Foveran.Syntax.Identifier

-- The only difference between this and InternalSyntax is the
-- appearance of explicit types in the “Case” expression, and explicit
-- types on the “Eq” type former. This is needed for correct
-- reflection of the variables during NBE.

type Term = Rec TermCon

data TermCon tm
    = Free  Ident
    | Bound Int
    | Lam   Ident tm
    | App   tm tm
    | Set   Int
    | Pi    (Maybe Ident) tm tm
    | Sigma (Maybe Ident) tm tm
    | Pair  tm tm
    | Proj1 tm
    | Proj2 tm
    | Sum   tm tm
    | Inl   tm
    | Inr   tm
    | Case  tm tm tm Ident tm Ident tm Ident tm
    | Unit
    | UnitI
    | Empty
    | ElimEmpty tm tm

    | Eq     tm tm tm tm
    | Refl
    | ElimEq tm tm tm tm Ident Ident tm tm

    | Desc
    | Desc_K    tm
    | Desc_Id
    | Desc_Prod tm tm
    | Desc_Sum  tm tm
    | Desc_Elim
    | Sem
    | Mu        tm
    | Construct tm
    | Induction
      
    {- Descriptions of indexed types -}
    | IDesc
    | IDesc_K    tm
    | IDesc_Id   tm
    | IDesc_Pair tm tm
    | IDesc_Sg   tm tm
    | IDesc_Pi   tm tm
    | IDesc_Elim
    | MuI        tm tm
    | InductionI
    deriving (Show, Functor)

--------------------------------------------------------------------------------
class Applicative f => Binding f where
    binder :: f a -> f a

instance Binding ((->) Int) where
    binder f i = f (i+1)

traverseSyn :: Binding f => TermCon (f a) -> f (TermCon a)
traverseSyn (Free nm')       = pure $ Free nm'
traverseSyn (Bound k)        = pure $ Bound k
traverseSyn (Lam nm body)    = Lam nm <$> binder body
traverseSyn (App t t')       = App <$> t <*> t'
traverseSyn (Set l)          = pure $ Set l
traverseSyn (Pi nm t1 t2)    = Pi nm <$> t1 <*> binder t2
traverseSyn (Sigma nm t1 t2) = Sigma nm <$> t1 <*> binder t2
traverseSyn (Pair t1 t2)     = Pair <$> t1 <*> t2
traverseSyn (Proj1 t)        = Proj1 <$> t
traverseSyn (Proj2 t)        = Proj2 <$> t
traverseSyn (Sum t1 t2)      = Sum <$> t1 <*> t2
traverseSyn (Inl t)          = Inl <$> t
traverseSyn (Inr t)          = Inr <$> t
traverseSyn (Case t1 tA tB x t2 y t3 z t4)
    = Case <$> t1
           <*> tA <*> tB
           <*> pure x <*> binder t2
           <*> pure y <*> binder t3
           <*> pure z <*> binder t4
traverseSyn Unit             = pure Unit
traverseSyn UnitI            = pure UnitI
traverseSyn Empty            = pure Empty
traverseSyn (ElimEmpty t1 t2) = ElimEmpty <$> t1 <*> t2

traverseSyn (Eq tA tB t1 t2) = Eq <$> tA <*> tB <*> t1 <*> t2
traverseSyn Refl             = pure Refl
traverseSyn (ElimEq tA ta tb t a e t1 t2) =
    ElimEq <$> tA <*> ta <*> tb <*> t <*> pure a <*> pure e <*> binder (binder t1) <*> t2

traverseSyn Desc             = pure Desc
traverseSyn (Desc_K t)       = Desc_K <$> t
traverseSyn Desc_Id          = pure Desc_Id
traverseSyn (Desc_Prod t1 t2)= Desc_Prod <$> t1 <*> t2
traverseSyn (Desc_Sum t1 t2) = Desc_Sum <$> t1 <*> t2
traverseSyn Desc_Elim        = pure Desc_Elim
traverseSyn Sem              = pure Sem
traverseSyn (Mu t)           = Mu <$> t
traverseSyn (Construct t)    = Construct <$> t
traverseSyn Induction        = pure Induction

traverseSyn IDesc            = pure IDesc
traverseSyn (IDesc_K t)      = IDesc_K <$> t
traverseSyn (IDesc_Id t)     = IDesc_Id <$> t
traverseSyn (IDesc_Pair t1 t2) = IDesc_Pair <$> t1 <*> t2
traverseSyn (IDesc_Sg t1 t2) = IDesc_Sg <$> t1 <*> t2
traverseSyn (IDesc_Pi t1 t2) = IDesc_Pi <$> t1 <*> t2
traverseSyn IDesc_Elim       = pure IDesc_Elim
traverseSyn (MuI t1 t2)      = MuI <$> t1 <*> t2
traverseSyn InductionI       = pure InductionI

--------------------------------------------------------------------------------
generaliseAlg :: [Term] -> Term -> TermCon (Int -> a) -> Int -> TermCon a
generaliseAlg searchTerms currentTerm x =
    case elemIndex currentTerm searchTerms of
      Nothing -> traverseSyn x
      Just k -> \i -> Bound (i+k)

-- return an open term where substituting subterm in will give the originalterm
generalise :: [Term] -> Term -> Term
generalise searchTerms originalTerm = go originalTerm 0
    where
      go t@(In x) = In <$> generaliseAlg searchTerms t (go <$> x)

--------------------------------------------------------------------------------
bindAlg :: [Ident] -> TermCon (Int -> a) -> Int -> TermCon a
bindAlg nms (Free nm) = \i -> case elemIndex nm nms of
                                Nothing -> Free nm
                                Just k  -> Bound (i + k)
bindAlg nms x         = traverseSyn x

bindFree :: [Ident] -> Term -> Term
bindFree nms x = translateRec (bindAlg nms) x 0

--------------------------------------------------------------------------------
gatheringLam :: Ident -> DS.Term -> DS.TermCon DS.Term
gatheringLam nm (In (DS.Lam nms body)) = DS.Lam (DS.PatVar nm:nms) body
gatheringLam nm body                   = DS.Lam [DS.PatVar nm] body

gatheringApp :: DS.Term -> DS.Term -> DS.TermCon DS.Term
gatheringApp (In (DS.App t1 t2)) t3 = DS.App t1 (t2 ++ [t3])
gatheringApp t1                  t2 = DS.App t1 [t2]

gatheringPi :: [DS.Pattern] -> DS.Term -> DS.Term -> DS.TermCon DS.Term
gatheringPi nm t1 (In (DS.Pi bs t2)) = DS.Pi ((nm,t1):bs) t2
gatheringPi nm t1 t2                 = DS.Pi [(nm,t1)] t2

gatheringTuple :: DS.Term -> DS.Term -> DS.TermCon DS.Term
gatheringTuple t1 (In (DS.Tuple tms)) = DS.Tuple (t1:tms)
gatheringTuple t1 t2                  = DS.Tuple [t1,t2]

toDisplay :: TermCon (NameSupply DS.Term) -> NameSupply (DS.TermCon DS.Term)
toDisplay (Free nm)               = pure $ DS.Var nm
toDisplay (Bound i)               = DS.Var <$> getBound i
toDisplay (Lam nm body)           = bindK nm body $ \nm body -> pure (gatheringLam nm body)
toDisplay (App t t')              = gatheringApp <$> t <*> t'
toDisplay (Set i)                 = pure $ DS.Set i
toDisplay (Pi Nothing t1 t2)      = gatheringPi [] <$> t1 <*> bindDummy t2
toDisplay (Pi (Just nm) t1 t2)    = bindK nm t2 $ \nm t2 -> gatheringPi [DS.PatVar nm] <$> t1 <*> pure t2
toDisplay (Sigma Nothing t1 t2)   = DS.Prod <$> t1 <*> bindDummy t2
toDisplay (Sigma (Just nm) t1 t2) = bindK nm t2 $ \nm t2 -> DS.Sigma [DS.PatVar nm] <$> t1 <*> pure t2
toDisplay (Pair t1 t2)            = gatheringTuple <$> t1 <*> t2
toDisplay (Proj1 t)               = DS.Proj1 <$> t
toDisplay (Proj2 t)               = DS.Proj2 <$> t
toDisplay (Sum t1 t2)             = DS.Sum <$> t1 <*> t2
toDisplay (Inl t)                 = DS.Inl <$> t
toDisplay (Inr t)                 = DS.Inr <$> t
toDisplay (Case t1 _ _ x t2 y t3 z t4)
    = bindK x t2 $ \x t2 ->
      bindK y t3 $ \y t3 ->
      bindK z t4 $ \z t4 -> DS.Case <$> t1
                                    <*> pure x <*> pure t2
                                    <*> pure (DS.PatVar y) <*> pure t3
                                    <*> pure (DS.PatVar z) <*> pure t4
toDisplay Unit                    = pure DS.Unit
toDisplay UnitI                   = pure DS.UnitI
toDisplay Empty                   = pure DS.Empty
toDisplay (ElimEmpty t1 t2)       = DS.ElimEmpty <$> t1 <*> (Just <$> t2)

toDisplay (Eq _ _ t1 t2)          = DS.Eq <$> t1 <*> t2
toDisplay Refl                    = pure DS.Refl
toDisplay (ElimEq _ _ _ t a e t1 t2) =
    do (a', (e', t1')) <- bind a (bind e t1)
       DS.ElimEq <$> t <*> ((\x y t -> Just (x,y,t)) <$> pure a' <*> pure e' <*> pure t1') <*> t2

toDisplay Desc                    = pure DS.Desc
toDisplay (Desc_K t)              = DS.Desc_K <$> t
toDisplay Desc_Id                 = pure DS.Desc_Id
toDisplay (Desc_Prod t1 t2)       = DS.Desc_Prod <$> t1 <*> t2
toDisplay (Desc_Sum t1 t2)        = DS.Desc_Sum <$> t1 <*> t2
toDisplay Desc_Elim               = pure DS.Desc_Elim
toDisplay Sem                     = pure DS.Sem
toDisplay (Mu t)                  = DS.Mu <$> t
toDisplay (Construct t)           = DS.Construct <$> t
toDisplay Induction               = pure DS.Induction

toDisplay IDesc                   = pure DS.IDesc
toDisplay (IDesc_Id t)            = DS.IDesc_Id <$> t
toDisplay (IDesc_K t)             = DS.Desc_K <$> t
toDisplay (IDesc_Pair t1 t2)      = DS.Desc_Prod <$> t1 <*> t2
toDisplay (IDesc_Sg t1 t2)        = DS.IDesc_Sg <$> t1 <*> t2
toDisplay (IDesc_Pi t1 t2)        = DS.IDesc_Pi <$> t1 <*> t2
toDisplay IDesc_Elim              = pure DS.IDesc_Elim
toDisplay (MuI t1 t2)             = DS.MuI <$> t1 <*> t2
toDisplay InductionI              = pure DS.InductionI

toDisplaySyntax :: Term -> NameSupply DS.Term
toDisplaySyntax = translateRec toDisplay

{------------------------------------------------------------------------------}
tmApp :: (Int -> Term) -> (Int -> Term) -> (Int -> Term)
tmApp t1 t2 = In <$> (App <$> t1 <*> t2)

tmFst :: (Int -> Term) -> (Int -> Term)
tmFst t = In . Proj1 <$> t

tmSnd :: (Int -> Term) -> (Int -> Term)
tmSnd t = In . Proj2 <$> t

tmInl :: (Int -> Term) -> (Int -> Term)
tmInl t = In . Inl <$> t

tmInr :: (Int -> Term) -> (Int -> Term)
tmInr t = In . Inr <$> t

vbound :: Int -> (Int -> Term)
vbound i j = In $ Bound (j - i - 1)

tmBound :: ((Int -> Term) -> (Int -> Term)) -> Int -> Term
tmBound f i = f (vbound i) (i+1)

tmFree :: Ident -> Int -> Term
tmFree nm = \i -> In $ Free nm

{------------------------------------------------------------------------------}
-- FIXME: some of these things are irrelevant: so they needn't be
-- checked for equality

-- FIXME: Should reimplement this with (optional) set-level
-- cummulativity checking
instance Eq Term where
  In (Free nm1) == In (Free nm2)     = nm1 == nm2
  In (Bound i)  == In (Bound j)      = i == j
  In (Lam _ t)  == In (Lam _ t')     = t == t'
  In (App t ts) == In (App t' ts')   = t == t' && ts == ts'
  In (Set i)    == In (Set j)        = i == j
  In (Pi _ t1 t2)    == In (Pi _ t1' t2')    = t1 == t1' && t2 == t2'
  In (Sigma _ t1 t2) == In (Sigma _ t1' t2') = t1 == t1' && t2 == t2'
  In (Sum t1 t2)     == In (Sum t1' t2')     = t1 == t1' && t2 == t2'
  In (Pair t1 t2)    == In (Pair t1' t2')    = t1 == t1' && t2 == t2'
  In (Proj1 t)  == In (Proj1 t')     = t == t'
  In (Proj2 t)  == In (Proj2 t')     = t == t'
  In (Inl t)    == In (Inl t')       = t == t'
  In (Inr t)    == In (Inr t')       = t == t'
  In (Case t1 _ _ _ t2 _ t3  _ t4) == In (Case t1' _ _ _ t2' _ t3' _ t4') = t1 == t1' && t2 == t2' && t3 == t3' && t4 == t4'
  In Unit       == In Unit           = True
  In UnitI      == In UnitI          = True
  In Empty      == In Empty          = True
  In (ElimEmpty t1 t2) == In (ElimEmpty t1' t2') = t1 == t1'

  In (Eq _ _ ta tb) == In (Eq _ _ ta' tb') = ta == ta' && tb == tb'
  In Refl           == In Refl             = True
  In (ElimEq _ _ _ t _ _ tP tp) == In (ElimEq _ _ _ t' _ _ tP' tp') = t == t' && tP == tP' && tp == tp'

  In Desc       == In Desc           = True
  In (Desc_K t) == In (Desc_K t')    = t == t'
  In Desc_Id    == In Desc_Id        = True
  In (Desc_Prod t1 t2) == In (Desc_Prod t1' t2') = t1 == t1' && t2 == t2'
  In (Desc_Sum t1 t2)  == In (Desc_Sum t1' t2')  = t1 == t1' && t2 == t2'
  In Desc_Elim  == In Desc_Elim      = True
  In Sem        == In Sem            = True
  In (Mu t)     == In (Mu t')        = t == t'
  In (Construct t) == In (Construct t') = t == t'
  In Induction  == In Induction      = True
  
  In IDesc      == In IDesc          = True
  In (IDesc_K t)   == In (IDesc_K t')              = t == t'
  In (IDesc_Id t)  == In (IDesc_Id t')             = t == t'
  In (IDesc_Pair t1 t2) == In (IDesc_Pair t1' t2') = t1 == t1' && t2 == t2'
  In (IDesc_Sg t1 t2)   == In (IDesc_Sg t1' t2')   = t1 == t1' && t2 == t2'
  In (IDesc_Pi t1 t2)   == In (IDesc_Pi t1' t2')   = t1 == t1' && t2 == t2'
  In IDesc_Elim == In IDesc_Elim     = True
  In (MuI t1 t2) == In (MuI t1' t2') = t1 == t1' && t2 == t2'
  In InductionI  == In InductionI    = True
  
  _             == _                 = False
