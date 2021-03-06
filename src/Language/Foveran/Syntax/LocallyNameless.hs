{-# LANGUAGE DeriveFunctor, TypeSynonymInstances, OverloadedStrings, TupleSections, FlexibleInstances #-}

module Language.Foveran.Syntax.LocallyNameless
    ( TermPos
    , TermCon (..)
    , GlobalFlag (..)
    , Binding (..)
    , bindingOfPattern
    , toLocallyNamelessClosed
    , toLocallyNameless
    , close
    )
    where

import           Text.Show.Functions ()
import           Data.Traversable (sequenceA, traverse)
import           Control.Applicative
import           Data.Rec
import           Text.Position (Span)
import           Data.FreeMonad
import           Data.Pair
import qualified Language.Foveran.Syntax.Display as DS
import           Language.Foveran.Syntax.Identifier (Ident)

type TermPos = AnnotRec Span TermCon
type TermPos' p = AnnotRec p TermCon

data GlobalFlag
    = IsGlobal
    | IsLocal
    deriving Show

data Binding
    = BindVar   Ident
    | BindTuple [Binding]
    | BindNull
    | BindRecur Ident
    deriving Show

data TermCon tm
  = Free  Ident GlobalFlag
  | Bound Int
  | Lam   Ident tm
  | App   tm tm
  | Set   Int
  | Pi    (Maybe Ident) tm tm
  | Sigma (Maybe Ident) tm tm
  | Tuple tm tm
  | Proj1 tm
  | Proj2 tm
  | Sum   tm tm
  | Inl   tm
  | Inr   tm
  | Case  tm (Maybe (Ident, tm)) Ident tm Ident tm
  | Unit  (Maybe Ident)
  | UnitI
  | Empty
  | ElimEmpty tm (Maybe tm)

  | Eq        tm tm
  | Refl
  | ElimEq    tm (Maybe (Ident, Ident, tm)) tm

  | Desc_K    tm
  | Desc_Prod tm tm
  | Construct tm
    
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
  | Eliminate  tm (Maybe (Ident, Ident, tm)) Ident Ident Ident tm

  | NamedConstructor Ident [tm]
  | CasesOn          Bool tm [(Ident, [DS.Pattern], [Binding] -> tm)]
    -- a suspended conversion to locally nameless, waiting for the additional variables to be bound

  | TypeAscrip tm tm

  | Generalise  tm tm

  | LabelledType Ident [Pair tm] tm
  | Return       tm
  | Call         tm

  | UserHole
  | Hole       Ident [tm]
  deriving (Show, Functor)

instance Show (TermPos' p) where
    show (Annot p t) = "(" ++ show t ++ ")"

--------------------------------------------------------------------------------
identOfPattern :: DS.Pattern -> Ident
identOfPattern (DS.PatVar nm)  = nm
identOfPattern (DS.PatTuple _) = "p" -- FIXME: concatenate all the names, or something
identOfPattern DS.PatNull      = "__x"

bindingOfPattern :: DS.Pattern -> Binding
bindingOfPattern (DS.PatVar nm)         = BindVar nm
bindingOfPattern (DS.PatTuple patterns) = BindTuple (map bindingOfPattern patterns)
bindingOfPattern DS.PatNull             = BindNull

--------------------------------------------------------------------------------
data Var -- FIXME: not sure if this the best way of doing things
    = VarNormal  Ident
    | VarRecurse Ident
    deriving Eq

lookupVarInBinding :: Var -> Binding -> FM TermCon a -> Maybe (FM TermCon a)
lookupVarInBinding v BindNull t =
    Nothing
lookupVarInBinding v (BindRecur nm) t
    | v == VarRecurse nm = Just t
    | otherwise          = Nothing
lookupVarInBinding v (BindVar nm) t
    | v == VarNormal nm  = Just t
    | otherwise          = Nothing
lookupVarInBinding v (BindTuple l) t =
    lookupVarInTupleBinding l t
    where
      lookupVarInTupleBinding []     t =
          Nothing
      lookupVarInTupleBinding [b]    t =
          lookupVarInBinding v b t
      lookupVarInTupleBinding (b:bs) t =
          lookupVarInBinding v b (Layer $ Proj1 t)
          <|>
          lookupVarInTupleBinding bs (Layer $ Proj2 t)

lookupVar :: Var -> [Binding] -> Int -> Maybe (FM TermCon a)
lookupVar v []     k = Nothing
lookupVar v (b:bs) k =
    lookupVarInBinding v b (Layer $ Bound k)
    <|>
    lookupVar v bs (k+1)

--------------------------------------------------------------------------------
toLN :: DS.TermCon ([Binding] -> a) -> [Binding] -> FM TermCon a
toLN (DS.Var nm)          bv = case lookupVar (VarNormal nm) bv 0 of
                                 Nothing -> Layer $ Free nm IsGlobal
                                 Just t  -> t
toLN (DS.Lam nms body)    bv = doBinders nms bv
    where
      doBinders []      bv = return $ body bv
      doBinders (p:nms) bv = Layer $ Lam (identOfPattern p) (doBinders nms (bindingOfPattern p:bv))
toLN (DS.App t ts)        bv = doApplications (return $ t bv) ts
    where doApplications tm []     = tm
          doApplications tm (t:ts) = doApplications (Layer $ App tm (return $ t bv)) ts
toLN (DS.Set i)           bv = Layer $ Set i
toLN (DS.Pi bs t)         bv = doArrows bs bv
    where doArrows []            bv = return $ t bv
          doArrows (([],t1):bs)  bv = Layer $ Pi Nothing (return $ t1 bv) (doArrows bs (BindNull:bv))
          doArrows ((nms,t1):bs) bv = doNames nms t1 bv (doArrows bs)

          doNames  []     t1 bv k = k bv
          doNames  (p:ps) t1 bv k = Layer $ Pi (Just $ identOfPattern p) (return $ t1 bv) (doNames ps t1 (bindingOfPattern p:bv) k)
toLN (DS.Sigma nms t1 t2) bv = doBinders nms bv
    where doBinders []       bv = return   $ t2 bv
          doBinders (nm:nms) bv = Layer $ Sigma (Just $ identOfPattern nm) (return $ t1 bv) (doBinders nms (bindingOfPattern nm:bv))
toLN (DS.Prod t1 t2)      bv = Layer $ Sigma Nothing (return $ t1 bv) (return $ t2 (BindNull:bv))
toLN (DS.Tuple tms)       bv = doTuple tms
    where doTuple []       = Layer $ UnitI
          doTuple [tm]     = Var $ tm bv
          doTuple (tm:tms) = Layer $ Tuple (Var $ tm bv) (doTuple tms)
toLN (DS.Proj1 t)         bv = Layer $ Proj1 (return $ t bv)
toLN (DS.Proj2 t)         bv = Layer $ Proj2 (return $ t bv)
toLN (DS.Sum t1 t2)       bv = Layer $ Sum (return $ t1 bv) (return $ t2 bv)
toLN (DS.Inl t)           bv = Layer $ Inl (return $ t bv)
toLN (DS.Inr t)           bv = Layer $ Inr (return $ t bv)
toLN (DS.Case t1 Nothing y t3 z t4) bv =
    Layer $ Case (return $ t1 bv)
                 Nothing
                 (identOfPattern y)
                 (return $ t3 (bindingOfPattern y:bv))
                 (identOfPattern z)
                 (return $ t4 (bindingOfPattern z:bv))
toLN (DS.Case t1 (Just (x, t2)) y t3 z t4) bv =
    Layer $ Case (return $ t1 bv)
                 (Just (x, return $ t2 (BindVar x:bv)))
                 (identOfPattern y)
                 (return $ t3 (bindingOfPattern y:bv))
                 (identOfPattern z)
                 (return $ t4 (bindingOfPattern z:bv))
toLN DS.Unit              bv = Layer $ Unit Nothing
toLN DS.UnitI             bv = Layer $ UnitI
toLN DS.Empty             bv = Layer $ Empty
toLN (DS.ElimEmpty t1 Nothing)   bv = Layer $ ElimEmpty (return $ t1 bv) Nothing
toLN (DS.ElimEmpty t1 (Just t2)) bv = Layer $ ElimEmpty (return $ t1 bv) (Just (return $ t2 bv))

toLN (DS.Eq t1 t2)        bv = Layer $ Eq (return $ t1 bv) (return $ t2 bv)
toLN DS.Refl              bv = Layer $ Refl
toLN (DS.ElimEq t t1 t2) bv =
    Layer $ ElimEq (return $ t bv)
                   ((\(x,y,t1) -> (x, y, return $ t1 (BindVar y:BindVar x:bv))) <$> t1)
                   (return $ t2 bv)

toLN (DS.Desc_K t)        bv = Layer $ Desc_K (return $ t bv)
toLN (DS.Desc_Prod t1 t2) bv = Layer $ Desc_Prod (return $ t1 bv) (return $ t2 bv)
toLN (DS.Construct t)     bv = Layer $ Construct (return $ t bv)

toLN DS.IDesc             bv = Layer $ IDesc
toLN (DS.IDesc_Id t)      bv = Layer $ IDesc_Id (return $ t bv)
toLN (DS.IDesc_Sg t1 t2)  bv = Layer $ IDesc_Sg (return $ t1 bv) (return $ t2 bv)
toLN (DS.IDesc_Pi t1 t2)  bv = Layer $ IDesc_Pi (return $ t1 bv) (return $ t2 bv)
toLN (DS.IDesc_Bind t1 x t2) bv =
    Layer $ IDesc_Bind (return $ t1 bv) (identOfPattern x) (return $ t2 (bindingOfPattern x:bv))
toLN DS.IDesc_Elim        bv = Layer $ IDesc_Elim
toLN (DS.SemI tD x tA)    bv =
    Layer $ SemI (return $ tD bv) (identOfPattern x) (return $ tA (bindingOfPattern x:bv))
toLN (DS.MapI tD i1 tA i2 tB tf tx) bv =
    Layer $ MapI (return $ tD bv)
                 (identOfPattern i1) (return $ tA (bindingOfPattern i1:bv))
                 (identOfPattern i2) (return $ tB (bindingOfPattern i2:bv))
                 (return $ tf bv)
                 (return $ tx bv)
toLN (DS.LiftI tD i tA i' a tP tx) bv =
    Layer $ LiftI (return $ tD bv)
                  (identOfPattern i) (return $ tA (bindingOfPattern i:bv))
                  (identOfPattern i') (identOfPattern a) (return $ tP (bindingOfPattern a:bindingOfPattern i':bv))
                  (return $ tx bv)
toLN (DS.MuI t1 t2)       bv = Layer $ MuI (return $ t1 bv) (return $ t2 bv)
toLN (DS.Eliminate t tP i x p tK) bv =
    Layer $ Eliminate (return $ t bv)
                      ((\(x,y,t) -> (identOfPattern x, identOfPattern y, return $ t (bindingOfPattern y:bindingOfPattern x:bv))) <$> tP)
                      (identOfPattern i)
                      (identOfPattern x)
                      (identOfPattern p)
                      (return $ tK (bindingOfPattern p:bindingOfPattern x:bindingOfPattern i:bv))

toLN (DS.NamedConstructor nm tms) bv =
    Layer $ NamedConstructor nm (map (\t -> return (t bv)) tms)
toLN (DS.CasesOn isRecursive tm clauses) bv =
    Layer $ CasesOn isRecursive
                    (return $ tm bv)
                    (map (\(ident,patterns,tm) -> (ident,patterns,\bv' -> return $ tm (bv' ++ bv))) clauses)
toLN (DS.RecurseOn nm) bv =
    case lookupVar (VarRecurse nm) bv 0 of
      Nothing -> Layer $ Free nm IsGlobal -- FIXME: should really throw an error
      Just t  -> t

toLN (DS.TypeAscrip t1 t2) bv = Layer $ TypeAscrip (return $ t1 bv) (return $ t2 bv)
toLN (DS.Generalise t1 t2) bv = Layer $ Generalise (return $ t1 bv) (return $ t2 bv)

toLN (DS.LabelledType nm args ty) bv =
    Layer $ LabelledType nm (map (fmap (\x -> return (x bv))) args) (return $ ty bv)
toLN (DS.Return t) bv =
    Layer $ Return (return $ t bv)
toLN (DS.Call t) bv =
    Layer $ Call (return $ t bv)

toLN DS.UserHole          bv = Layer $ UserHole
toLN (DS.Hole nm tms)     bv = Layer $ Hole nm (map (\t -> return (t bv)) tms)

toLocallyNamelessClosed :: AnnotRec a DS.TermCon -> AnnotRec a TermCon
toLocallyNamelessClosed t = translateStar toLN t []

toLocallyNameless :: AnnotRec a DS.TermCon -> [Binding] -> AnnotRec a TermCon
toLocallyNameless t = translateStar toLN t

{------------------------------------------------------------------------------}
binder :: (Int -> a) -> Int -> a
binder f i = f (i+1)

close' :: [Ident] -> TermCon (Int -> a) -> Int -> TermCon a
close' fnm (Free nm global) = pure $ Free nm global
close' fnm (Bound k)        = \i -> if k < i then Bound k
                                    else let j = k - i
                                             l = length fnm
                                         in if j < length fnm
                                            then Free (fnm !! j) IsLocal
                                            else Bound (k - l)
close' fnm (Lam nm body)    = Lam nm <$> binder body
close' fnm (App t ts)       = App <$> t <*> ts
close' fnm (Set i)          = pure $ Set i
close' fnm (Pi nm t1 t2)    = Pi nm <$> t1 <*> binder t2
close' fnm (Sigma nm t1 t2) = Sigma nm <$> t1 <*> binder t2
close' fnm (Tuple t1 t2)    = Tuple <$> t1 <*> t2
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
close' fnm (Unit tag)       = pure (Unit tag)
close' fnm UnitI            = pure UnitI
close' fnm Empty            = pure Empty
close' fnm (ElimEmpty t1 t2) = ElimEmpty <$> t1 <*> sequenceA t2

close' fnm (Eq t1 t2)       = Eq <$> t1 <*> t2
close' fnm Refl             = pure Refl
close' fnm (ElimEq t Nothing t2) = ElimEq <$> t <*> pure Nothing <*> t2
close' fnm (ElimEq t (Just (x,y,t1)) t2) = ElimEq <$> t <*> ((\t1 -> Just (x,y,t1)) <$> binder (binder t1)) <*> t2

close' fnm (Desc_K t)       = Desc_K <$> t
close' fnm (Desc_Prod t1 t2)= Desc_Prod <$> t1 <*> t2
close' fnm (Construct t)    = Construct <$> t

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
close' fnm (Eliminate t tP i x p tK) =
    Eliminate <$> t
              <*> traverse (\(i,x,tP) -> (i,x,) <$> binder (binder tP)) tP
              <*> pure i <*> pure x <*> pure p <*> binder (binder (binder tK))
close' fnm (NamedConstructor nm tms) = NamedConstructor nm <$> sequenceA tms
close' fnm (CasesOn isRecursive tm clauses) =
    CasesOn <$> pure isRecursive
            <*> tm
            <*> sequenceA (map (\(ident,patterns,tm) i -> (ident,patterns,\bv' -> tm bv' (i + length bv'))) clauses)

close' fnm UserHole         = pure UserHole
close' fnm (Hole nm tms)    = Hole nm <$> sequenceA tms

close' fnm (TypeAscrip tm ty) = TypeAscrip <$> tm <*> ty

close' fnm (Generalise t1 t2) = Generalise <$> t1 <*> t2

close' fnm (LabelledType nm args ty) =
    LabelledType nm <$> traverse sequenceA args <*> ty
close' fnm (Return t) =
    Return <$> t
close' fnm (Call t) =
    Call <$> t

close :: [Ident] -> AnnotRec a TermCon -> Int -> AnnotRec a TermCon
close nms x offset = translate (close' nms) x offset
