{-# LANGUAGE TypeSynonymInstances, DeriveFunctor #-}

module Foveran.Syntax.Checked where

import Control.Applicative
import Data.Rec
import qualified Foveran.Syntax.Display as DS
import Foveran.NameSupply

-- The only difference between this and InternalSyntax is the
-- appearance of explicit types in the “Case” expression. This is
-- needed for correct reflection of the variables during NBE.

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
    | ElimEmpty
    | Desc
    | Desc_K    tm
    | Desc_Id
    | Desc_Prod tm tm
    | Desc_Sum  tm tm
    | Desc_Elim
    | Mu        tm
    | Construct
    | Induction
      
    {- Descriptions of indexed types -}
    | IDesc
    | IDesc_K
    | IDesc_Id
    | IDesc_Pair
    | IDesc_Sg
    | IDesc_Pi

    | IDesc_Elim
    deriving (Show, Functor)

--------------------------------------------------------------------------------
binder :: (Int -> a) -> Int -> a
binder f i = f (i+1)

bind' :: Ident -> TermCon (Int -> a) -> Int -> TermCon a
bind' fnm (Free nm')       = \i -> if fnm == nm' then Bound i else Free nm'
bind' fnm (Bound k)        = pure $ Bound k
bind' fnm (Lam nm body)    = Lam nm <$> binder body
bind' fnm (App t t')       = App <$> t <*> t'
bind' fnm (Set l)          = pure $ Set l
bind' fnm (Pi nm t1 t2)    = Pi nm <$> t1 <*> binder t2
bind' fnm (Sigma nm t1 t2) = Sigma nm <$> t1 <*> binder t2
bind' fnm (Pair t1 t2)     = Pair <$> t1 <*> t2
bind' fnm (Proj1 t)        = Proj1 <$> t
bind' fnm (Proj2 t)        = Proj2 <$> t
bind' fnm (Sum t1 t2)      = Sum <$> t1 <*> t2
bind' fnm (Inl t)          = Inl <$> t
bind' fnm (Inr t)          = Inr <$> t
bind' fnm (Case t1 tA tB x t2 y t3 z t4)
                          = Case <$> t1
                                 <*> tA <*> tB
                                 <*> pure x <*> binder t2
                                 <*> pure y <*> binder t3
                                 <*> pure z <*> binder t4
bind' fnm Unit             = pure Unit
bind' fnm UnitI            = pure UnitI
bind' fnm Empty            = pure Empty
bind' fnm ElimEmpty        = pure ElimEmpty
bind' fnm Desc             = pure Desc
bind' fnm (Desc_K t)       = Desc_K <$> t
bind' fnm Desc_Id          = pure Desc_Id
bind' fnm (Desc_Prod t1 t2)= Desc_Prod <$> t1 <*> t2
bind' fnm (Desc_Sum t1 t2) = Desc_Sum <$> t1 <*> t2
bind' fnm Desc_Elim        = pure Desc_Elim
bind' fnm (Mu t)           = Mu <$> t
bind' fnm Construct        = pure Construct
bind' fnm Induction        = pure Induction

bind' fnm IDesc            = pure IDesc
bind' fnm IDesc_K          = pure IDesc_K
bind' fnm IDesc_Id         = pure IDesc_Id
bind' fnm IDesc_Pair       = pure IDesc_Pair
bind' fnm IDesc_Sg         = pure IDesc_Sg
bind' fnm IDesc_Pi         = pure IDesc_Pi
bind' fnm IDesc_Elim       = pure IDesc_Elim

bindFree :: Ident -> Term -> Term
bindFree nm x = translateRec (bind' nm) x 0

--------------------------------------------------------------------------------
gatheringLam :: Ident -> DS.Term -> DS.TermCon DS.Term
gatheringLam nm (In (DS.Lam nms body)) = DS.Lam (nm:nms) body
gatheringLam nm body                   = DS.Lam [nm] body

gatheringApp :: DS.Term -> DS.Term -> DS.TermCon DS.Term
gatheringApp (In (DS.App t1 t2)) t3 = DS.App t1 (t2 ++ [t3])
gatheringApp t1                  t2 = DS.App t1 [t2]

-- FIXME: this is wrong: should put the newly chosen name in at the
-- binders
toDisplay :: NameSupply f => TermCon (f DS.Term) -> f (DS.TermCon DS.Term)
toDisplay (Free nm)               = pure $ DS.Var nm
toDisplay (Bound i)               = DS.Var <$> getBound i
toDisplay (Lam nm body)           = gatheringLam nm <$> bind nm body
toDisplay (App t t')              = gatheringApp <$> t <*> t'
toDisplay (Set i)                 = pure $ DS.Set i
toDisplay (Pi Nothing t1 t2)      = DS.Arr <$> t1 <*> bindDummy t2
toDisplay (Pi (Just nm) t1 t2)    = DS.Pi [nm] <$> t1 <*> bind nm t2
toDisplay (Sigma Nothing t1 t2)   = DS.Prod <$> t1 <*> bindDummy t2
toDisplay (Sigma (Just nm) t1 t2) = DS.Sigma [nm] <$> t1 <*> bind nm t2
toDisplay (Pair t1 t2)            = DS.Pair <$> t1 <*> t2
toDisplay (Proj1 t)               = DS.Proj1 <$> t
toDisplay (Proj2 t)               = DS.Proj2 <$> t
toDisplay (Sum t1 t2)             = DS.Sum <$> t1 <*> t2
toDisplay (Inl t)                 = DS.Inl <$> t
toDisplay (Inr t)                 = DS.Inr <$> t
toDisplay (Case t1 _ _ x t2 y t3 z t4)
                                  = DS.Case <$> t1
                                            <*> pure x <*> bind x t2
                                            <*> pure y <*> bind y t3
                                            <*> pure z <*> bind z t4
toDisplay Unit                    = pure DS.Unit
toDisplay UnitI                   = pure DS.UnitI
toDisplay Empty                   = pure DS.Empty
toDisplay ElimEmpty               = pure DS.ElimEmpty
toDisplay Desc                    = pure DS.Desc
toDisplay (Desc_K t)              = DS.Desc_K <$> t
toDisplay Desc_Id                 = pure DS.Desc_Id
toDisplay (Desc_Prod t1 t2)       = DS.Desc_Prod <$> t1 <*> t2
toDisplay (Desc_Sum t1 t2)        = DS.Desc_Sum <$> t1 <*> t2
toDisplay Desc_Elim               = pure DS.Desc_Elim
toDisplay (Mu t)                  = DS.Mu <$> t
toDisplay Construct               = pure DS.Construct
toDisplay Induction               = pure DS.Induction

toDisplay IDesc                   = pure DS.IDesc
toDisplay IDesc_Id                = pure DS.IDesc_Id
toDisplay IDesc_K                 = pure DS.IDesc_K
toDisplay IDesc_Pair              = pure DS.IDesc_Pair
toDisplay IDesc_Sg                = pure DS.IDesc_Sg
toDisplay IDesc_Pi                = pure DS.IDesc_Pi
toDisplay IDesc_Elim              = pure DS.IDesc_Elim

toDisplaySyntax :: NameSupply f => Term -> f DS.Term
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
  In ElimEmpty  == In ElimEmpty      = True
  In Desc       == In Desc           = True
  In (Desc_K t) == In (Desc_K t')    = t == t'
  In Desc_Id    == In Desc_Id        = True
  In (Desc_Prod t1 t2) == In (Desc_Prod t1' t2') = t1 == t1' && t2 == t2'
  In (Desc_Sum t1 t2)  == In (Desc_Sum t1' t2')  = t1 == t1' && t2 == t2'
  In Desc_Elim  == In Desc_Elim      = True
  In (Mu t)     == In (Mu t')        = t == t'
  In Construct  == In Construct      = True
  In Induction  == In Induction      = True
  
  In IDesc      == In IDesc          = True
  In IDesc_K    == In IDesc_K        = True
  In IDesc_Id   == In IDesc_Id       = True
  In IDesc_Pair == In IDesc_Pair     = True
  In IDesc_Sg   == In IDesc_Sg       = True
  In IDesc_Pi   == In IDesc_Pi       = True
  In IDesc_Elim == In IDesc_Elim     = True
  
  _             == _                 = False
