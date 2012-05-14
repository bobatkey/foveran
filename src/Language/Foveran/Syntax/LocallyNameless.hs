{-# LANGUAGE DeriveFunctor, TypeSynonymInstances, OverloadedStrings, TupleSections, FlexibleInstances #-}

module Language.Foveran.Syntax.LocallyNameless
    ( TermPos
    , TermCon (..)
    , Abelian (..)
    , toLocallyNamelessClosed
    , toLocallyNameless
    , close
    )
    where

import           Data.Traversable (sequenceA, traverse)
import           Control.Applicative
import           Data.Rec
import           Text.Position (Span)
import           Data.FreeMonad
import qualified Language.Foveran.Syntax.Display as DS
import           Language.Foveran.Syntax.Identifier (Ident)
import           Language.Foveran.Syntax.Common (Abelian)

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
  | Case  tm (Maybe (Ident, tm)) Ident tm Ident tm
  | Unit
  | UnitI
  | Empty
  | ElimEmpty tm (Maybe tm)

  | Eq        tm tm
  | Refl
  | ElimEq    tm (Maybe (Ident, Ident, tm)) tm

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
  | IDesc_Bind tm Ident tm
  | IDesc_Elim
  | SemI       tm Ident tm
  | LiftI      tm Ident tm Ident Ident tm tm
  | MapI       tm Ident tm Ident tm tm tm
  | MuI        tm tm
  | InductionI

  | Group      Ident Abelian (Maybe tm)
  | GroupUnit
  | GroupMul   tm tm
  | GroupInv   tm

  | UserHole
  | Hole       Ident [tm]
  deriving (Show, Functor)

instance Show (TermPos' p) where
    show (Annot p t) = "(" ++ show t ++ ")"

identOfPattern (DS.PatVar nm)  = nm
identOfPattern (DS.PatTuple _) = "p" -- FIXME: concatenate all the names, or something
identOfPattern DS.PatNull      = "__x"

lookupVarInPattern :: Ident -> DS.Pattern -> Int -> Maybe (FM TermCon a)
lookupVarInPattern nm (DS.PatVar nm') k | nm == nm' = Just (Layer $ Bound k)
                                        | otherwise = Nothing
lookupVarInPattern nm (DS.PatTuple l) k = do
  (t, isLast) <- lookupVarInTuplePattern l
  return $ if isLast then t else (Layer $ Proj1 t)
    where lookupVarInTuplePattern []     = Nothing
          lookupVarInTuplePattern [p]    = do t <- lookupVarInPattern nm p k; return (t, True)
          lookupVarInTuplePattern (p:ps) = do t <- lookupVarInPattern nm p k; return (t, False)
                                           <|>
                                           do (t,isLast) <- lookupVarInTuplePattern ps; return (Layer $ Proj2 t, isLast)
lookupVarInPattern nm (DS.PatNull)    k = Nothing

lookupVar :: Ident -> [DS.Pattern] -> Int -> Maybe (FM TermCon a)
lookupVar nm []     k = Nothing
lookupVar nm (p:ps) k = lookupVarInPattern nm p k <|> lookupVar nm ps (k+1)

toLN :: DS.TermCon ([DS.Pattern] -> a) -> [DS.Pattern] -> FM TermCon a
toLN (DS.Var nm)          bv = case lookupVar nm bv 0 of
                                 Nothing -> Layer $ Free nm
                                 Just t  -> t
toLN (DS.Lam nms body)    bv = doBinders nms bv
    where
      doBinders []      bv = return $ body bv
      doBinders (p:nms) bv = Layer $ Lam (identOfPattern p) (doBinders nms (p:bv))
toLN (DS.App t ts)        bv = doApplications (return $ t bv) ts
    where doApplications tm []     = tm
          doApplications tm (t:ts) = doApplications (Layer $ App tm (return $ t bv)) ts
toLN (DS.Set i)           bv = Layer $ Set i
toLN (DS.Pi bs t)         bv = doArrows bs bv
    where doArrows []            bv = return $ t bv
          doArrows (([],t1):bs)  bv = Layer $ Pi Nothing (return $ t1 bv) (doArrows bs (DS.PatNull:bv))
          doArrows ((nms,t1):bs) bv = doNames nms t1 bv (doArrows bs)

          doNames  []       t1 bv k = k bv
          doNames  (nm:nms) t1 bv k = Layer $ Pi (Just $ identOfPattern nm) (return $ t1 bv) (doNames nms t1 (nm:bv) k)
toLN (DS.Sigma nms t1 t2) bv = doBinders nms bv
    where doBinders []       bv = return   $ t2 bv
          doBinders (nm:nms) bv = Layer $ Sigma (Just $ identOfPattern nm) (return $ t1 bv) (doBinders nms (nm:bv))
toLN (DS.Prod t1 t2)      bv = Layer $ Sigma Nothing (return $ t1 bv) (return $ t2 (DS.PatNull:bv))
toLN (DS.Tuple tms)       bv = doTuple tms
    where doTuple []       = Layer $ Unit
          doTuple [tm]     = Var $ tm bv
          doTuple (tm:tms) = Layer $ Pair (Var $ tm bv) (doTuple tms)
toLN (DS.Proj1 t)         bv = Layer $ Proj1 (return $ t bv)
toLN (DS.Proj2 t)         bv = Layer $ Proj2 (return $ t bv)
toLN (DS.Sum t1 t2)       bv = Layer $ Sum (return $ t1 bv) (return $ t2 bv)
toLN (DS.Inl t)           bv = Layer $ Inl (return $ t bv)
toLN (DS.Inr t)           bv = Layer $ Inr (return $ t bv)
toLN (DS.Case t1 Nothing y t3 z t4) bv =
    Layer $ Case (return $ t1 bv)
                 Nothing
                 (identOfPattern y)
                 (return $ t3 (y:bv))
                 (identOfPattern z)
                 (return $ t4 (z:bv))
toLN (DS.Case t1 (Just (x, t2)) y t3 z t4) bv =
    Layer $ Case (return $ t1 bv)
                 (Just (x, return $ t2 (DS.PatVar x:bv)))
                 (identOfPattern y)
                 (return $ t3 (y:bv))
                 (identOfPattern z)
                 (return $ t4 (z:bv))
toLN DS.Unit              bv = Layer $ Unit
toLN DS.UnitI             bv = Layer $ UnitI
toLN DS.Empty             bv = Layer $ Empty
toLN (DS.ElimEmpty t1 Nothing)   bv = Layer $ ElimEmpty (return $ t1 bv) Nothing
toLN (DS.ElimEmpty t1 (Just t2)) bv = Layer $ ElimEmpty (return $ t1 bv) (Just (return $ t2 bv))

toLN (DS.Eq t1 t2)        bv = Layer $ Eq (return $ t1 bv) (return $ t2 bv)
toLN DS.Refl              bv = Layer $ Refl
toLN (DS.ElimEq t t1 t2) bv =
    Layer $ ElimEq (return $ t bv)
                   ((\(x,y,t1) -> (x, y, return $ t1 (DS.PatVar y:DS.PatVar x:bv))) <$> t1)
                   (return $ t2 bv)

toLN DS.Desc              bv = Layer $ Desc
toLN (DS.Desc_K t)        bv = Layer $ Desc_K (return $ t bv)
toLN DS.Desc_Id           bv = Layer $ Desc_Id
toLN (DS.Desc_Prod t1 t2) bv = Layer $ Desc_Prod (return $ t1 bv) (return $ t2 bv)
toLN (DS.Desc_Sum t1 t2)  bv = Layer $ Desc_Sum (return $ t1 bv) (return $ t2 bv)
toLN DS.Desc_Elim         bv = Layer $ Desc_Elim
toLN DS.Sem               bv = Layer $ Sem
toLN (DS.Mu t)            bv = Layer $ Mu (return $ t bv)
toLN (DS.Construct t)     bv = Layer $ Construct (return $ t bv)
toLN DS.Induction         bv = Layer $ Induction

toLN DS.IDesc             bv = Layer $ IDesc
toLN (DS.IDesc_Id t)      bv = Layer $ IDesc_Id (return $ t bv)
toLN (DS.IDesc_Sg t1 t2)  bv = Layer $ IDesc_Sg (return $ t1 bv) (return $ t2 bv)
toLN (DS.IDesc_Pi t1 t2)  bv = Layer $ IDesc_Pi (return $ t1 bv) (return $ t2 bv)
toLN (DS.IDesc_Bind t1 x t2) bv =
    Layer $ IDesc_Bind (return $ t1 bv) (identOfPattern x) (return $ t2 (x:bv))
toLN DS.IDesc_Elim        bv = Layer $ IDesc_Elim
toLN (DS.SemI tD x tA)    bv =
    Layer $ SemI (return $ tD bv) (identOfPattern x) (return $ tA (x:bv))
toLN (DS.MapI tD i1 tA i2 tB tf tx) bv =
    Layer $ MapI (return $ tD bv)
                 (identOfPattern i1) (return $ tA (i1:bv))
                 (identOfPattern i2) (return $ tB (i2:bv))
                 (return $ tf bv)
                 (return $ tx bv)
toLN (DS.LiftI tD i tA i' a tP tx) bv =
    Layer $ LiftI (return $ tD bv)
                  (identOfPattern i) (return $ tA (i:bv))
                  (identOfPattern i') (identOfPattern a) (return $ tP (a:i':bv))
                  (return $ tx bv)
toLN (DS.MuI t1 t2)       bv = Layer $ MuI (return $ t1 bv) (return $ t2 bv)
toLN DS.InductionI        bv = Layer $ InductionI

toLN (DS.Group nm ab ty)  bv = Layer $ Group nm ab ((return . ($bv)) <$> ty)
toLN DS.GroupUnit         bv = Layer $ GroupUnit
toLN (DS.GroupMul t1 t2)  bv = Layer $ GroupMul (return $ t1 bv) (return $ t2 bv)
toLN (DS.GroupInv t)      bv = Layer $ GroupInv (return $ t bv)

toLN DS.UserHole          bv = Layer $ UserHole
toLN (DS.Hole nm tms)     bv = Layer $ Hole nm (map (\t -> return (t bv)) tms)

toLocallyNamelessClosed :: AnnotRec a DS.TermCon -> AnnotRec a TermCon
toLocallyNamelessClosed t = translateStar toLN t []

toLocallyNameless :: AnnotRec a DS.TermCon -> [DS.Pattern] -> AnnotRec a TermCon
toLocallyNameless t = translateStar toLN t

{------------------------------------------------------------------------------}
binder :: (Int -> a) -> Int -> a
binder f i = f (i+1)

close' :: [Ident] -> TermCon (Int -> a) -> Int -> TermCon a
close' fnm (Free nm)        = pure $ Free nm
close' fnm (Bound k)        = \i -> if k < i then Bound k
                                    else let j = k - i
                                             l = length fnm
                                         in if j < length fnm then Free (fnm !! j)
                                            else Bound (k - l)
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
close' fnm (Case t1 tP y t3 z t4) =
    Case <$> t1
         <*> traverse (\(x,tP) -> (x,) <$> binder tP) tP
         <*> pure y <*> binder t3
         <*> pure z <*> binder t4
close' fnm Unit             = pure Unit
close' fnm UnitI            = pure UnitI
close' fnm Empty            = pure Empty
close' fnm (ElimEmpty t1 t2) = ElimEmpty <$> t1 <*> sequenceA t2

close' fnm (Eq t1 t2)       = Eq <$> t1 <*> t2
close' fnm Refl             = pure Refl
close' fnm (ElimEq t Nothing t2) = ElimEq <$> t <*> pure Nothing <*> t2
close' fnm (ElimEq t (Just (x,y,t1)) t2) = ElimEq <$> t <*> ((\t1 -> Just (x,y,t1)) <$> binder (binder t1)) <*> t2

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
close' fnm (IDesc_Bind t1 x t2) = IDesc_Bind <$> t1 <*> pure x <*> binder t2
close' fnm IDesc_Elim       = pure IDesc_Elim
close' fnm (SemI tD x tA)   = SemI <$> tD <*> pure x <*> binder tA
close' fnm (MapI tD i1 tA i2 tB tf tx) =
    MapI <$> tD <*> pure i1 <*> binder tA <*> pure i2 <*> binder tB <*> tf <*> tx
close' fnm (MuI t1 t2)      = MuI <$> t1 <*> t2
close' fnm (LiftI tD i tA i' a tP tx) =
    LiftI <$> tD <*> pure i <*> binder tA <*> pure i' <*> pure a <*> binder (binder tP) <*> tx
close' fnm InductionI       = pure InductionI
close' fnm UserHole         = pure UserHole
close' fnm (Hole nm tms)    = Hole nm <$> sequenceA tms

close' fnm (Group nm ab ty) = Group nm ab <$> sequenceA ty
close' fnm GroupUnit        = pure GroupUnit
close' fnm (GroupMul t1 t2) = GroupMul <$> t1 <*> t2
close' fnm (GroupInv t)     = GroupInv <$> t

close :: [Ident] -> AnnotRec a TermCon -> Int -> AnnotRec a TermCon
close nms x offset = translate (close' nms) x offset
