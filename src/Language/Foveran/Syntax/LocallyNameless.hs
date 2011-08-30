{-# LANGUAGE DeriveFunctor, TypeSynonymInstances #-}

module Language.Foveran.Syntax.LocallyNameless
    ( Ident
    , TermPos
    , TermCon (..)
    , toLocallyNameless
    , close
    , close1
    )
    where

import           Data.List (elemIndex)
import           Control.Applicative
import           Data.Rec
import           Text.Position (Span)
import           Data.FreeMonad
import qualified Data.Text as T
import qualified Language.Foveran.Syntax.Display as DS
import           Language.Foveran.Syntax.Identifier (Ident)

type TermPos = AnnotRec Span TermCon
type TermPos' p = AnnotRec p TermCon

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
  | Case  tm Ident tm Ident tm Ident tm
  | Unit
  | UnitI
  | Empty
  | ElimEmpty

  | Eq        tm tm
  | Refl
  | ElimEq    tm Ident Ident tm tm

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
    
  | IDesc
  | IDesc_Id   tm
  | IDesc_Sg   tm tm
  | IDesc_Pi   tm tm
  | IDesc_Elim
  | MuI        tm tm
  | InductionI
  deriving (Show, Functor)

instance Show (TermPos' p) where
    show (Annot p t) = "(" ++ show t ++ ")"


toLN :: DS.TermCon ([Ident] -> a) -> [Ident] -> FM TermCon a
toLN (DS.Var nm)          bv = Layer $ case elemIndex nm bv of
                                         Nothing -> Free nm
                                         Just i  -> Bound i
toLN (DS.Lam nms body)    bv = doBinders nms bv
    where doBinders []       bv = Var   $ body bv
          doBinders (nm:nms) bv = Layer $ Lam nm (doBinders nms (nm:bv))
toLN (DS.App t ts)        bv = doApplications (Var $ t bv) ts
    where doApplications tm []     = tm
          doApplications tm (t:ts) = doApplications (Layer $ App tm (Var $ t bv)) ts
toLN (DS.Set i)           bv = Layer $ Set i
toLN (DS.Pi nms t1 t2)    bv = doBinders nms bv
    where doBinders []       bv = Var   $ t2 bv
          doBinders (nm:nms) bv = Layer $ Pi (Just nm) (Var $ t1 bv) (doBinders nms (nm:bv))
toLN (DS.Arr t1 t2)       bv = Layer $ Pi Nothing (Var $ t1 bv) (Var $ t2 (T.empty:bv))
toLN (DS.Sigma nms t1 t2) bv = doBinders nms bv
    where doBinders []       bv = Var   $ t2 bv
          doBinders (nm:nms) bv = Layer $ Sigma (Just nm) (Var $ t1 bv) (doBinders nms (nm:bv))
toLN (DS.Prod t1 t2)      bv = Layer $ Sigma Nothing (Var $ t1 bv) (Var $ t2 (T.empty:bv))
toLN (DS.Pair t1 t2)      bv = Layer $ Pair (Var $ t1 bv) (Var $ t2 bv)
toLN (DS.Proj1 t)         bv = Layer $ Proj1 (Var $ t bv)
toLN (DS.Proj2 t)         bv = Layer $ Proj2 (Var $ t bv)
toLN (DS.Sum t1 t2)       bv = Layer $ Sum (Var $ t1 bv) (Var $ t2 bv)
toLN (DS.Inl t)           bv = Layer $ Inl (Var $ t bv)
toLN (DS.Inr t)           bv = Layer $ Inr (Var $ t bv)
toLN (DS.Case t1 x t2 y t3 z t4) bv = Layer $ Case (Var $ t1 bv)
                                                   x
                                                   (Var $ t2 (x:bv))
                                                   y
                                                   (Var $ t3 (y:bv))
                                                   z
                                                   (Var $ t4 (z:bv))
toLN DS.Unit              bv = Layer $ Unit
toLN DS.UnitI             bv = Layer $ UnitI
toLN DS.Empty             bv = Layer $ Empty
toLN DS.ElimEmpty         bv = Layer $ ElimEmpty

toLN (DS.Eq t1 t2)        bv = Layer $ Eq (Var $ t1 bv) (Var $ t2 bv)
toLN DS.Refl              bv = Layer $ Refl
toLN (DS.ElimEq t x y t1 t2) bv =
    Layer $ ElimEq (Var $ t bv)
                   x y (Var $ t1 (y:x:bv))
                   (Var $ t2 bv)

toLN DS.Desc              bv = Layer $ Desc
toLN (DS.Desc_K t)        bv = Layer $ Desc_K (Var $ t bv)
toLN DS.Desc_Id           bv = Layer $ Desc_Id
toLN (DS.Desc_Prod t1 t2) bv = Layer $ Desc_Prod (Var $ t1 bv) (Var $ t2 bv)
toLN (DS.Desc_Sum t1 t2)  bv = Layer $ Desc_Sum (Var $ t1 bv) (Var $ t2 bv)
toLN DS.Desc_Elim         bv = Layer $ Desc_Elim
toLN DS.Sem               bv = Layer $ Sem
toLN (DS.Mu t)            bv = Layer $ Mu (Var $ t bv)
toLN (DS.Construct t)     bv = Layer $ Construct (Var $ t bv)
toLN DS.Induction         bv = Layer $ Induction

toLN DS.IDesc             bv = Layer $ IDesc
toLN (DS.IDesc_Id t)      bv = Layer $ IDesc_Id (Var $ t bv)
toLN (DS.IDesc_Sg t1 t2)  bv = Layer $ IDesc_Sg (Var $ t1 bv) (Var $ t2 bv)
toLN (DS.IDesc_Pi t1 t2)  bv = Layer $ IDesc_Pi (Var $ t1 bv) (Var $ t2 bv)
toLN DS.IDesc_Elim        bv = Layer $ IDesc_Elim
toLN (DS.MuI t1 t2)       bv = Layer $ MuI (Var $ t1 bv) (Var $ t2 bv)
toLN DS.InductionI        bv = Layer $ InductionI

toLocallyNameless :: AnnotRec a DS.TermCon -> AnnotRec a TermCon
toLocallyNameless t = translateStar toLN t []

{------------------------------------------------------------------------------}
binder :: (Int -> a) -> Int -> a
binder f i = f (i+1)

close' :: Ident -> TermCon (Int -> a) -> Int -> TermCon a
close' fnm (Free nm)        = pure $ Free nm
close' fnm (Bound k)        = \i -> if i == k then Free fnm else Bound k
close' fnm (Lam nm body)    = Lam nm <$> binder body
close' fnm (App t ts)       = App <$> t <*> ts
close' fnm (Set i)          = pure $ Set i
close' fnm (Pi nm t1 t2)    = Pi nm <$> t1 <*> binder t2
close' fnm (Sigma nm t1 t2) = Sigma nm <$> t1 <*> binder t2
close' fnm (Pair t1 t2)     = Pair <$> t1 <*> t2
close' fnm (Proj1 t)        = Proj1 <$> t
close' fnm (Proj2 t)        = Proj2 <$> t
close' fnm (Sum t1 t2)      = Sum <$> t1 <*> t2
close' fnm (Inl t)          = Inl <$> t
close' fnm (Inr t)          = Inr <$> t
close' fnm (Case t1 x t2 y t3 z t4) = Case <$> t1
                                           <*> pure x <*> binder t2
                                           <*> pure y <*> binder t3
                                           <*> pure z <*> binder t4
close' fnm Unit             = pure Unit
close' fnm UnitI            = pure UnitI
close' fnm Empty            = pure Empty
close' fnm ElimEmpty        = pure ElimEmpty

close' fnm (Eq t1 t2)       = Eq <$> t1 <*> t2
close' fnm Refl             = pure Refl
close' fnm (ElimEq t x y t1 t2) = ElimEq <$> t <*> pure x <*> pure y <*> binder (binder t1) <*> t2

close' fnm Desc             = pure Desc
close' fnm (Desc_K t)       = Desc_K <$> t
close' fnm Desc_Id          = pure Desc_Id
close' fnm (Desc_Prod t1 t2)= Desc_Prod <$> t1 <*> t2
close' fnm (Desc_Sum t1 t2) = Desc_Sum <$> t1 <*> t2
close' fnm Desc_Elim        = pure Desc_Elim
close' fnm Sem              = pure Sem
close' fnm (Mu t)           = Mu <$> t
close' fnm (Construct t)    = Construct <$> t
close' fnm Induction        = pure Induction

close' fnm IDesc            = pure IDesc
close' fnm (IDesc_Id t)     = IDesc_Id <$> t
close' fnm (IDesc_Sg t1 t2) = IDesc_Sg <$> t1 <*> t2
close' fnm (IDesc_Pi t1 t2) = IDesc_Pi <$> t1 <*> t2
close' fnm IDesc_Elim       = pure IDesc_Elim
close' fnm (MuI t1 t2)      = MuI <$> t1 <*> t2
close' fnm InductionI       = pure InductionI

close :: Ident -> AnnotRec a TermCon -> AnnotRec a TermCon
close fnm x = translate (close' fnm) x 0

close1 :: Ident -> AnnotRec a TermCon -> AnnotRec a TermCon
close1 fnm x = translate (close' fnm) x 1
