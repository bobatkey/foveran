module FunctorNBE where

import Text.Show.Functions
import Control.Applicative

data Type
    = B | Type :=> Type | Type :*: Type | F Type
    deriving (Eq, Show)

infixr 5 :=>
infixr 6 :*:

data Term
    = Var  Int
    | Free Type String
    | Lam  Type Term
    | App  Term Term
    | Pair Term Term
    | Fst  Term
    | Snd  Term
    | Map  Type Type
    deriving (Eq, Show)

type TermFam = Int -> Term

data Value
    = VLam     (Value -> Value)
    | VPair    Value Value
    | VFunctor (Type -> (Value -> TermFam) -> TermFam)
    | VNeutral TermFam
    deriving Show

--------------------------------------------------------------------------------
($$) :: Value -> Value -> Value
VLam f $$ v = f v

vfst :: Value -> Value
vfst (VPair v _) = v

vsnd :: Value -> Value
vsnd (VPair _ v) = v

--------------------------------------------------------------------------------
eval :: Term -> [(Type,Value)] -> Value
eval (Var i) = \env -> snd (env !! i)
eval (Free ty nm) = pure (reflect ty (pure $ Free ty nm))
eval (Lam ty t)   = \env -> VLam $ \v -> eval t ((ty,v):env)
eval (App t1 t2)  = ($$) <$> eval t1 <*> eval t2
eval (Pair t1 t2) = VPair <$> eval t1 <*> eval t2
eval (Fst t)      = vfst <$> eval t
eval (Snd t)      = vsnd <$> eval t
eval (Map a b)    = pure (VLam $ \(VLam f) ->
                          VLam $ \(VFunctor g) ->
                          VFunctor (\c h -> g c (h . f)))

vbound :: Int -> TermFam
vbound i j = Var (j - i - 1)

reify :: Type -> Value -> TermFam
reify B         (VNeutral t)  = t
reify (a :=> b) (VLam f)      = \i -> let d = reflect a (vbound i)
                                      in Lam a (reify b (f d) (i+1))
reify (a :*: b) (VPair v1 v2) = Pair <$> reify a v1 <*> reify b v2
reify (F a)     (VFunctor v)  = v a (reify a)

reflect :: Type -> TermFam -> Value
reflect B         t = VNeutral t
reflect (a :=> b) t = VLam $ \v -> reflect b (App <$> t <*> reify a v)
reflect (a :*: b) t = VPair (reflect a (Fst <$> t)) (reflect b (Snd <$> t))
reflect (F a)     t = VFunctor $ \b f i -> Map a b `App` (Lam a $ f (reflect b (vbound i)) (i+1)) `App` t i

normalise :: Term -> Type -> Term
normalise tm ty = reify ty (eval tm []) 0

--------------------------------------------------------------------------------
tm1 = Lam (B :=> B) (Var 0)
ty1 = (B :=> B) :=> (B :=> B)

tm2 = Lam (F B) (Var 0)
ty2 = F B :=> F B

tm3 = Lam (B :=> B) $ Lam (F B) $ Map B B `App` Var 1 `App` (Map B B `App` Var 1 `App` Var 0)
ty3 = (B :=> B) :=> F B :=> F B