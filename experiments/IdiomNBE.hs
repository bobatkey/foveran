module IdiomNBE where

import Text.Show.Functions
import Control.Applicative

data Type
    = B | Type :=> Type | De Type | Type :*: Type
    deriving (Eq, Show)

infixr 5 :=>
infixr 6 :*:

data Term
    = Var  Int
    | Free Type String
    | Lam  Type Term
    | App  Term Term
    | Pure Term
    | Ap   Term Term
    | Pair Term Term
    | Fst  Term
    | Snd  Term
    deriving Show

data Value
    = VLam     (Value -> Value)
    | VPair    Value Value
    | VNeutral (Int -> Term)
    | VIdiom   (VIdiom Value)
    deriving Show

data VIdiom a
    = Stop a
    | Step Type (Int -> Term) (VIdiom (Value -> a))
    deriving Show

instance Functor VIdiom where
    fmap f (Stop a)     = Stop (f a)
    fmap f (Step t e c) = Step t e (fmap (fmap f) c)

instance Applicative VIdiom where
    pure = Stop
    (Stop f)     <*> a = fmap f a
    (Step t e c) <*> a = Step t e (fmap flip c <*> a)

--------------------------------------------------------------------------------
($$) :: Value -> Value -> Value
VLam f $$ v = f v

vpure :: Value -> Value
vpure v = VIdiom (Stop v)

unVLam (VLam f) = f

vap :: Value -> Value -> Value
vap (VIdiom f) (VIdiom a) = VIdiom ((unVLam <$> f) <*> a)

vfst :: Value -> Value
vfst (VPair v _) = v

vsnd :: Value -> Value
vsnd (VPair _ v) = v

--------------------------------------------------------------------------------
eval :: Term -> [(Type,Value)] -> Value
eval (Var i)      = \env -> snd (env !! i)
eval (Free ty nm) = pure (reflect ty (pure $ Free ty nm))
eval (Lam ty t)   = \env -> VLam $ \v -> eval t ((ty,v):env)
eval (App t1 t2)  = ($$) <$> eval t1 <*> eval t2
eval (Pure t)     = vpure <$> eval t
eval (Ap t1 t2)   = vap <$> eval t1 <*> eval t2
eval (Pair t1 t2) = VPair <$> eval t1 <*> eval t2
eval (Fst t)      = vfst <$> eval t
eval (Snd t)      = vsnd <$> eval t

vbound :: Int -> (Int -> Term)
vbound i j = Var (j - i - 1)

reify :: Type -> Value -> (Int -> Term)
reify B         (VNeutral t)  = t
reify (a :=> b) (VLam f)      = \i -> let d = reflect a (vbound i)
                                     in Lam a (reify b (f d) (i + 1))
reify (De a)    (VIdiom c)    = reifyIdiom a c
reify (a :*: b) (VPair v1 v2) = Pair <$> reify a v1 <*> reify b v2

reifyIdiom a (Stop v)     = Pure <$> reify a v
reifyIdiom a (Step b t k) = Ap <$> reifyIdiom (b :=> a) (VLam <$> k) <*> t

reflect :: Type -> (Int -> Term) -> Value
reflect (a :=> b) t = VLam $ \v -> reflect b (App <$> t <*> reify a v)
reflect B         t = VNeutral t
reflect (De a)    t = VIdiom (Step a t $ Stop id)
reflect (a :*: b) t = VPair (reflect a (Fst <$> t)) (reflect b (Snd <$> t))

normalise :: Term -> Type -> Term
normalise tm ty = reify ty (eval tm []) 0

--------------------------------------------------------------------------------
tm1 = Lam (B :=> B :=> B) $ Lam (De B) $ Pure (Var 1) `Ap` Var 0 `Ap` Var 0
ty1 = (B :=> B :=> B) :=> De B :=> De B
