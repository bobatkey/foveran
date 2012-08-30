{-# LANGUAGE TypeSynonymInstances, DeriveFunctor, FlexibleInstances #-}

module Language.Foveran.Syntax.Checked
    ( Ident

    , Irrelevant (..)

    , Abelian (..)

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

    , cmp
    )
    where

import           Control.Applicative
import           Data.Rec
import           Data.List (elemIndex)
import           Data.Traversable
import qualified Language.Foveran.Syntax.Display as DS
import           Language.Foveran.Syntax.Identifier
import           Language.Foveran.Syntax.Common (Abelian)

newtype Irrelevant a = Irrelevant { fromIrrelevant :: a }
    deriving (Show)

instance Eq (Irrelevant a) where
    _ == _ = True

instance Ord (Irrelevant a) where
    compare _ _ = EQ

type Term = Rec TermCon

data TermCon tm
    = Free  Ident
    | Bound Int
    | Lam   (Irrelevant Ident) tm
    | App   tm tm
    | Set   Int
    | Pi    (Irrelevant (Maybe Ident)) tm tm
    | Sigma (Irrelevant (Maybe Ident)) tm tm
    | Pair  tm tm
    | Proj1 tm
    | Proj2 tm
    | Sum   tm tm
    | Inl   tm
    | Inr   tm
    | Case  tm tm tm (Irrelevant Ident) tm (Irrelevant Ident) tm (Irrelevant Ident) tm
    | Unit  (Irrelevant (Maybe Ident))
    | UnitI
    | Empty
    | ElimEmpty tm tm

    | Eq     tm tm tm tm
    | Refl
    | ElimEq tm tm tm tm (Irrelevant Ident) (Irrelevant Ident) tm tm

    | Desc
    | Desc_K    tm
    | Desc_Id
    | Desc_Prod tm tm
    | Desc_Sum  tm tm
    | Desc_Elim
    | Sem
    | Mu        tm
    | Construct (Irrelevant (Maybe Ident)) tm
    | Induction
      
    {- Descriptions of indexed types -}
    | IDesc
    | IDesc_K    tm
    | IDesc_Id   tm
    | IDesc_Pair tm tm
    | IDesc_Sg   tm tm
    | IDesc_Pi   tm tm
    | IDesc_Bind tm tm tm (Irrelevant Ident) tm
    | IDesc_Elim
    | MuI        tm tm
    | SemI       tm tm (Irrelevant Ident) tm
    | MapI       tm tm (Irrelevant Ident) tm (Irrelevant Ident) tm tm tm
    | LiftI      tm tm (Irrelevant Ident) tm (Irrelevant Ident) (Irrelevant Ident) tm tm
    | Eliminate  tm tm tm tm
                 (Irrelevant Ident) (Irrelevant Ident) tm
                 (Irrelevant Ident) (Irrelevant Ident) (Irrelevant Ident) tm

    {- Group stuff -}
    | Group      Ident Abelian (Maybe tm)
    | GroupUnit
    | GroupMul   tm tm
    | GroupInv   tm

    | Hole       Ident [tm]
    deriving (Show, Functor, Eq, Ord)

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
traverseSyn (Unit tag)       = pure (Unit tag)
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
traverseSyn (Construct tag t)= Construct tag <$> t
traverseSyn Induction        = pure Induction

traverseSyn IDesc            = pure IDesc
traverseSyn (IDesc_K t)      = IDesc_K <$> t
traverseSyn (IDesc_Id t)     = IDesc_Id <$> t
traverseSyn (IDesc_Pair t1 t2) = IDesc_Pair <$> t1 <*> t2
traverseSyn (IDesc_Sg t1 t2) = IDesc_Sg <$> t1 <*> t2
traverseSyn (IDesc_Pi t1 t2) = IDesc_Pi <$> t1 <*> t2
traverseSyn (IDesc_Bind tA tB t1 x t2) = IDesc_Bind <$> tA <*> tB <*> t1 <*> pure x <*> binder t2
traverseSyn IDesc_Elim       = pure IDesc_Elim
traverseSyn (SemI tI tD x tA)= SemI <$> tI <*> tD <*> pure x <*> binder tA
traverseSyn (MapI tI tD i1 tA i2 tB tf tx) =
    MapI <$> tI <*> tD <*> pure i1 <*> binder tA <*> pure i2 <*> binder tB <*> tf <*> tx
traverseSyn (LiftI tI tD i tA i' a tP tx) =
    LiftI <$> tI <*> tD <*> pure i <*> binder tA <*> pure i' <*> pure a <*> binder (binder tP) <*> tx
traverseSyn (MuI t1 t2)      = MuI <$> t1 <*> t2
traverseSyn (Eliminate tI tD ti t i1 x1 tP i2 x2 p2 tK) =
    Eliminate <$> tI <*> tD <*> ti <*> t
              <*> pure i1 <*> pure x1 <*> binder (binder tP)
              <*> pure i2 <*> pure x2 <*> pure p2 <*> binder (binder (binder tK))

traverseSyn (Group nm ab ty) = Group nm ab <$> sequenceA ty
traverseSyn GroupUnit        = pure GroupUnit
traverseSyn (GroupMul t1 t2) = GroupMul <$> t1 <*> t2
traverseSyn (GroupInv t)     = GroupInv <$> t

traverseSyn (Hole nm tms)    = Hole nm <$> sequenceA tms

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
bindAlg nms (Bound k) = \i -> if k >= i then Bound (i + length nms + k)
                              else Bound k
bindAlg nms (Free nm) = \i -> case elemIndex nm nms of
                                Nothing -> Free nm
                                Just k  -> Bound (i + k)
bindAlg nms x         = traverseSyn x

bindFree :: [Ident] -> Term -> Int -> Term
bindFree nms x offset = translateRec (bindAlg nms) x offset

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

toDisplay :: TermCon (NameGeneration DS.Term) -> NameGeneration (DS.TermCon DS.Term)
toDisplay (Free nm)               = pure $ DS.Var nm
toDisplay (Bound i)               = DS.Var <$> getBound i
toDisplay (Lam inm body)          = bindK nm body $ \nm body -> pure (gatheringLam nm body)
    where nm = fromIrrelevant inm
toDisplay (App t t')              = gatheringApp <$> t <*> t'
toDisplay (Set i)                 = pure $ DS.Set i
toDisplay (Pi (Irrelevant Nothing) t1 t2)
    = gatheringPi [] <$> t1 <*> bindDummy t2
toDisplay (Pi (Irrelevant (Just nm)) t1 t2)
    = bindK nm t2 $ \nm t2 -> gatheringPi [DS.PatVar nm] <$> t1 <*> pure t2
toDisplay (Sigma (Irrelevant Nothing) t1 t2)
    = DS.Prod <$> t1 <*> bindDummy t2
toDisplay (Sigma (Irrelevant (Just nm)) t1 t2)
    = bindK nm t2 $ \nm t2 -> DS.Sigma [DS.PatVar nm] <$> t1 <*> pure t2
toDisplay (Pair t1 t2)            = gatheringTuple <$> t1 <*> t2
toDisplay (Proj1 t)               = DS.Proj1 <$> t
toDisplay (Proj2 t)               = DS.Proj2 <$> t
toDisplay (Sum t1 t2)             = DS.Sum <$> t1 <*> t2
toDisplay (Inl t)                 = DS.Inl <$> t
toDisplay (Inr t)                 = DS.Inr <$> t
toDisplay (Case t1 _ _ ix t2 iy t3 iz t4)
    = bindK x t2 $ \x t2 ->
      bindK y t3 $ \y t3 ->
      bindK z t4 $ \z t4 -> DS.Case <$> t1
                                    <*> (Just <$> ((,) <$> pure x <*> pure t2))
                                    <*> pure (DS.PatVar y) <*> pure t3
                                    <*> pure (DS.PatVar z) <*> pure t4
    where x = fromIrrelevant ix
          y = fromIrrelevant iy
          z = fromIrrelevant iz
toDisplay (Unit tag)              = pure DS.Unit
toDisplay UnitI                   = pure DS.UnitI
toDisplay Empty                   = pure DS.Empty
toDisplay (ElimEmpty t1 t2)       = DS.ElimEmpty <$> t1 <*> (Just <$> t2)

toDisplay (Eq _ _ t1 t2)          = DS.Eq <$> t1 <*> t2
toDisplay Refl                    = pure DS.Refl
toDisplay (ElimEq _ _ _ t ia ie t1 t2) =
    do (a', (e', t1')) <- bind a (bind e t1)
       DS.ElimEq <$> t <*> ((\x y t -> Just (x,y,t)) <$> pure a' <*> pure e' <*> pure t1') <*> t2
    where a = fromIrrelevant ia
          e = fromIrrelevant ie

toDisplay Desc                    = pure DS.Desc
toDisplay (Desc_K t)              = DS.Desc_K <$> t
toDisplay Desc_Id                 = pure DS.Desc_Id
toDisplay (Desc_Prod t1 t2)       = DS.Desc_Prod <$> t1 <*> t2
toDisplay (Desc_Sum t1 t2)        = DS.Desc_Sum <$> t1 <*> t2
toDisplay Desc_Elim               = pure DS.Desc_Elim
toDisplay Sem                     = pure DS.Sem
toDisplay (Mu t)                  = DS.Mu <$> t
toDisplay (Construct (Irrelevant Nothing) t) =
    DS.Construct <$> t
toDisplay (Construct (Irrelevant (Just nm)) t) =
    DS.NamedConstructor <$> pure nm <*> (gatherParts <$> t)
        where gatherParts (In (DS.Tuple l)) = tail (init l)
              gatherParts _ = error "internal: malformed constructor found"
toDisplay Induction               = pure DS.Induction

toDisplay IDesc                   = pure DS.IDesc
toDisplay (IDesc_Id t)            = DS.IDesc_Id <$> t
toDisplay (IDesc_K t)             = DS.Desc_K <$> t
toDisplay (IDesc_Pair t1 t2)      = DS.Desc_Prod <$> t1 <*> t2
toDisplay (IDesc_Sg t1 t2)        = DS.IDesc_Sg <$> t1 <*> t2
toDisplay (IDesc_Pi t1 t2)        = DS.IDesc_Pi <$> t1 <*> t2
toDisplay (IDesc_Bind tA tB t1 ix t2) =
    bindK x t2 $ \x t2 -> DS.IDesc_Bind <$> t1 <*> pure (DS.PatVar x) <*> pure t2
    where x = fromIrrelevant ix
toDisplay IDesc_Elim              = pure DS.IDesc_Elim
toDisplay (SemI _ tD ix tA)       = bindK x tA $ \x tA -> DS.SemI <$> tD <*> pure (DS.PatVar x) <*> pure tA
    where x = fromIrrelevant ix
toDisplay (MapI _ tD ii1 tA ii2 tB tf tx) =
    bindK i1 tA $ \i1 tA ->
    bindK i2 tB $ \i2 tB ->
    DS.MapI <$> tD <*> pure (DS.PatVar i1) <*> pure tA <*> pure (DS.PatVar i2) <*> pure tB <*> tf <*> tx
    where i1 = fromIrrelevant ii1
          i2 = fromIrrelevant ii2
toDisplay (LiftI _ tD ix tA ii ia tP tx) =
    do (x', tA') <- bind x tA
       (i', (a', tP')) <- bind i (bind a tP)
       DS.LiftI <$> tD <*> pure (DS.PatVar x') <*> pure tA' <*> pure (DS.PatVar i') <*> pure (DS.PatVar a') <*> pure tP' <*> tx
    where x = fromIrrelevant ix
          i = fromIrrelevant ii
          a = fromIrrelevant ia
toDisplay (MuI t1 t2)             = DS.MuI <$> t1 <*> t2
toDisplay (Eliminate _ _ _ t ii1 ix1 tP ii2 ix2 ip2 tK) =
    do (i1', (x1', tP')) <- bind i1 (bind x1 tP)
       (i2', (x2', (p2', tK'))) <- bind i2 (bind x2 (bind p2 tK))
       DS.Eliminate <$> t
                    <*> pure (Just (DS.PatVar i1',DS.PatVar x1',tP'))
                    <*> pure (DS.PatVar i2') <*> pure (DS.PatVar x2') <*> pure (DS.PatVar p2') <*> pure tK'
    where i1 = fromIrrelevant ii1
          x1 = fromIrrelevant ix1
          i2 = fromIrrelevant ii2
          x2 = fromIrrelevant ix2
          p2 = fromIrrelevant ip2

toDisplay (Group nm ab paramTy)   = DS.Group nm ab <$> sequenceA paramTy
toDisplay GroupUnit               = pure DS.GroupUnit
toDisplay (GroupMul t1 t2)        = DS.GroupMul <$> t1 <*> t2
toDisplay (GroupInv t)            = DS.GroupInv <$> t

toDisplay (Hole nm tms)           = DS.Hole nm <$> sequenceA tms

toDisplaySyntax :: Term -> NameGeneration DS.Term
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
cmp :: (Int -> Int -> Bool)
    -> Term
    -> Term
    -> Bool
cmp compareLevel (In (Free nm1))         (In (Free nm2))         = nm1 == nm2
cmp compareLevel (In (Bound i))          (In (Bound j))          = i == j
cmp compareLevel (In (Lam _ t))          (In (Lam _ t'))         = cmp compareLevel t t'
cmp compareLevel (In (App t1 t2))        (In (App t1' t2'))      = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'
cmp compareLevel (In (Pi _ t1 t2))       (In (Pi _ t1' t2'))     = cmp (flip compareLevel) t1 t1' && cmp compareLevel t2 t2'

cmp compareLevel (In (Set i))            (In (Set j))            = compareLevel i j

cmp compareLevel (In (Sigma _ t1 t2))    (In (Sigma _ t1' t2'))  = cmp (==) t1 t1' && cmp compareLevel t2 t2' -- FIXME: is this right?
cmp compareLevel (In (Pair t1 t2))       (In (Pair t1' t2'))     = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'
cmp compareLevel (In (Proj1 t))          (In (Proj1 t'))         = cmp compareLevel t t'
cmp compareLevel (In (Proj2 t))          (In (Proj2 t'))         = cmp compareLevel t t'

cmp compareLevel (In (Sum t1 t2))        (In (Sum t1' t2'))      = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'
cmp compareLevel (In (Inl t))            (In (Inl t'))           = cmp compareLevel t t'
cmp compareLevel (In (Inr t))            (In (Inr t'))           = cmp compareLevel t t'
cmp compareLevel (In (Case t1  tA  tB  _ t2  _ t3  _ t4))
                 (In (Case t1' tA' tB' _ t2' _ t3' _ t4'))
    = cmp compareLevel t1 t1' &&
      cmp compareLevel tA tA' &&
      cmp compareLevel tB tB' &&
      cmp compareLevel t2 t2' &&
      cmp compareLevel t3 t3' &&
      cmp compareLevel t4 t4'

cmp compareLevel (In (Unit _))          (In (Unit _))            = True
cmp compareLevel (In UnitI)             (In UnitI)               = True
cmp compareLevel (In Empty)             (In Empty)               = True
cmp compareLevel (In (ElimEmpty t1 t2)) (In (ElimEmpty t1' t2')) = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'

cmp compareLevel (In (Eq tA tB ta tb))
                 (In (Eq tA' tB' ta' tb'))
    = cmp compareLevel ta ta' &&
      cmp compareLevel tb tb' &&
      cmp compareLevel tA tA' &&
      cmp compareLevel tB tB'
cmp compareLevel (In Refl)              (In Refl)                = True
cmp compareLevel (In (ElimEq tA  ta  tb  t  _ _ tP  tp))
                 (In (ElimEq tA' ta' tb' t' _ _ tP' tp'))
    = cmp compareLevel tA tA' &&
      cmp compareLevel ta ta' &&
      cmp compareLevel tb tb' &&
      cmp compareLevel t t'   &&
      cmp compareLevel tP tP' &&
      cmp compareLevel tp tp'

cmp compareLevel (In Desc)              (In Desc)                = True
cmp compareLevel (In (Desc_K t))        (In (Desc_K t'))         = cmp compareLevel t t'
cmp compareLevel (In Desc_Id)           (In Desc_Id)             = True
cmp compareLevel (In (Desc_Prod t1 t2)) (In (Desc_Prod t1' t2')) = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'
cmp compareLevel (In (Desc_Sum t1 t2))  (In (Desc_Sum t1' t2'))  = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'
cmp compareLevel (In Desc_Elim)         (In Desc_Elim)           = True
cmp compareLevel (In Sem)               (In Sem)                 = True
cmp compareLevel (In (Mu t))            (In (Mu t'))             = cmp compareLevel t t'
cmp compareLevel (In (Construct _ t))   (In (Construct _ t'))    = cmp compareLevel t t'
cmp compareLevel (In Induction)         (In Induction)           = True

cmp compareLevel (In IDesc)             (In IDesc)               = True
cmp compareLevel (In (IDesc_K t))       (In (IDesc_K t'))        = cmp compareLevel t t'
cmp compareLevel (In (IDesc_Id t))      (In (IDesc_Id t'))       = cmp compareLevel t t'
cmp compareLevel (In (IDesc_Pair t1 t2)) (In (IDesc_Pair t1' t2')) = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'
cmp compareLevel (In (IDesc_Sg t1 t2))  (In (IDesc_Sg t1' t2'))  = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'
cmp compareLevel (In (IDesc_Pi t1 t2))  (In (IDesc_Pi t1' t2'))  = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'
cmp compareLevel (In (IDesc_Bind tA  tB  t1  _ t2))
                 (In (IDesc_Bind tA' tB' t1' _ t2'))
    = cmp compareLevel tA tA' &&
      cmp compareLevel tB tB' &&
      cmp compareLevel t1 t1' &&
      cmp compareLevel t2 t2'
cmp compareLevel (In IDesc_Elim)        (In IDesc_Elim)          = True
cmp compareLevel (In (SemI tI  tD  _ tA))
                 (In (SemI tI' tD' _ tA'))
    = cmp compareLevel tI tI' &&
      cmp compareLevel tD tD' &&
      cmp compareLevel tA tA'
cmp compareLevel (In (MapI tI  tD  _ tA  _ tB  tf  tx))
                 (In (MapI tI' tD' _ tA' _ tB' tf' tx'))
    = cmp compareLevel tI tI' &&
      cmp compareLevel tD tD' &&
      cmp compareLevel tA tA' &&
      cmp compareLevel tB tB' &&
      cmp compareLevel tf tf' &&
      cmp compareLevel tx tx'
cmp compareLevel (In (MuI t1 t2))      (In (MuI t1' t2'))       = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'
cmp compareLevel (In (LiftI tI  tD  _ tA  _ _ tP  tx))
                 (In (LiftI tI' tD' _ tA' _ _ tP' tx'))
    = cmp compareLevel tI tI' &&
      cmp compareLevel tD tD' &&
      cmp compareLevel tA tA' &&
      cmp compareLevel tP tP' &&
      cmp compareLevel tx tx'
cmp compareLevel (In (Eliminate tI  tD  ti  tx  _ _ tP  _ _ _ tK))
                 (In (Eliminate tI' tD' ti' tx' _ _ tP' _ _ _ tK'))
    = all id [ cmp (==) tI tI'
             , cmp (==) tD tD'
             , cmp (==) ti ti'
             , cmp (==) tx tx'
             , cmp (==) tP tP' -- FIXME: should this be variant? should the other elimination forms be invariant in any position?
             , cmp (==) tK tK'
             ]

cmp compareLevel (In (Group nm ab Nothing)) (In (Group nm' ab' Nothing))
    = nm == nm' && ab == ab'
cmp compareLevel (In (Group nm ab (Just t))) (In (Group nm' ab' (Just t')))
    = nm == nm' && ab == ab' && cmp (==) t t' -- FIXME: I think this is right, wrt to the levels
cmp compareLevel (In GroupUnit)        (In GroupUnit)
    = True
cmp compareLevel (In (GroupMul t1 t2)) (In (GroupMul t1' t2'))
    = cmp compareLevel t1 t1' && cmp compareLevel t2 t2'
cmp compareLevel (In (GroupInv t))     (In (GroupInv t'))
    = cmp compareLevel t t'

cmp compareLevel (In (Hole nm tms))    (In (Hole nm' tms'))
    = nm == nm' && length tms == length tms' && all (uncurry (cmp compareLevel)) (zip tms tms') -- FIXME: write a proper comparison

cmp compareLevel _ _ = False


instance Eq Term where
    In tm == In tm' = tm == tm'

instance Ord Term where
    compare (In tm) (In tm') = compare tm tm'