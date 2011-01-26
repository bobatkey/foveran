{-# LANGUAGE DeriveFunctor #-}

module Language.Foveran.Syntax.LocallyNameless
    ( Ident
    , TermPos
    , TermCon (..)
    , toLocallyNameless
    , close
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
  | Desc
  | Desc_K    tm
  | Desc_Id
  | Desc_Prod tm tm
  | Desc_Sum  tm tm
  | Desc_Elim
  | Mu        tm
  | Construct
  | Induction
    
  | IDesc
  | IDesc_K
  | IDesc_Id
  | IDesc_Pair
  | IDesc_Sg
  | IDesc_Pi
  | IDesc_Elim
  deriving (Show, Functor)

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
toLN DS.Desc              bv = Layer $ Desc
toLN (DS.Desc_K t)        bv = Layer $ Desc_K (Var $ t bv)
toLN DS.Desc_Id           bv = Layer $ Desc_Id
toLN (DS.Desc_Prod t1 t2) bv = Layer $ Desc_Prod (Var $ t1 bv) (Var $ t2 bv)
toLN (DS.Desc_Sum t1 t2)  bv = Layer $ Desc_Sum (Var $ t1 bv) (Var $ t2 bv)
toLN DS.Desc_Elim         bv = Layer $ Desc_Elim
toLN (DS.Mu t)            bv = Layer $ Mu (Var $ t bv)
toLN DS.Construct         bv = Layer $ Construct
toLN DS.Induction         bv = Layer $ Induction

toLN DS.IDesc             bv = Layer $ IDesc
toLN DS.IDesc_K           bv = Layer $ IDesc_K
toLN DS.IDesc_Id          bv = Layer $ IDesc_Id
toLN DS.IDesc_Pair        bv = Layer $ IDesc_Pair
toLN DS.IDesc_Sg          bv = Layer $ IDesc_Sg
toLN DS.IDesc_Pi          bv = Layer $ IDesc_Pi
toLN DS.IDesc_Elim        bv = Layer $ IDesc_Elim

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
close' fnm Desc             = pure Desc
close' fnm (Desc_K t)       = Desc_K <$> t
close' fnm Desc_Id          = pure Desc_Id
close' fnm (Desc_Prod t1 t2)= Desc_Prod <$> t1 <*> t2
close' fnm (Desc_Sum t1 t2) = Desc_Sum <$> t1 <*> t2
close' fnm Desc_Elim        = pure Desc_Elim
close' fnm (Mu t)           = Mu <$> t
close' fnm Construct        = pure Construct
close' fnm Induction        = pure Induction

close' fnm IDesc            = pure IDesc
close' fnm IDesc_K          = pure IDesc_K
close' fnm IDesc_Id         = pure IDesc_Id
close' fnm IDesc_Pair       = pure IDesc_Pair
close' fnm IDesc_Sg         = pure IDesc_Sg
close' fnm IDesc_Pi         = pure IDesc_Pi
close' fnm IDesc_Elim       = pure IDesc_Elim

close :: Ident -> AnnotRec a TermCon -> AnnotRec a TermCon
close fnm x = translate (close' fnm) x 0
