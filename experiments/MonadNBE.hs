module MonadNBE where

import Text.Show.Functions
import Control.Applicative

data Type
    = B | Type :=> Type | Type :*: Type | T Type
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
    | Return Term
    | Bind   Term Term
    deriving (Eq, Show)

type TermFam = Int -> Term

data Value
    = VLam     (Value -> Value)
    | VPair    Value Value
    | VNeutral TermFam
    | VMonad   (VMonad Value)
    deriving Show

data VMonad a
    = VReturn a
    | VBind   Type (Int -> Term) (Value -> VMonad a)
    deriving Show

instance Monad VMonad where
    return = VReturn
    VReturn a   >>= f = f a
    VBind t e k >>= f = VBind t e (\v -> k v >>= f)

--------------------------------------------------------------------------------
($$) :: Value -> Value -> Value
VLam f $$ v = f v

vfst :: Value -> Value
vfst (VPair v _) = v

vsnd :: Value -> Value
vsnd (VPair _ v) = v

vreturn :: Value -> Value
vreturn = VMonad . return

unVMonad :: Value -> VMonad Value
unVMonad (VMonad vm) = vm

vbind v f = VMonad $ unVMonad v >>= unVMonad . f

--------------------------------------------------------------------------------
eval :: Term -> [Value] -> Value
eval (Var i) = \env -> env !! i
eval (Free ty nm) = pure (reflect ty (pure $ Free ty nm))
eval (Lam ty t)   = \env -> VLam $ \v -> eval t (v:env)
eval (App t1 t2)  = ($$) <$> eval t1 <*> eval t2
eval (Pair t1 t2) = VPair <$> eval t1 <*> eval t2
eval (Fst t)      = vfst <$> eval t
eval (Snd t)      = vsnd <$> eval t
eval (Return t)   = vreturn <$> eval t
eval (Bind t1 t2) = vbind <$> eval t1 <*> (\env v -> eval t2 (v:env))

vbound :: Int -> TermFam
vbound i j = Var (j - i - 1)

reify :: Type -> Value -> TermFam
reify B         (VNeutral t)  = t
reify (a :=> b) (VLam f)      = \i -> let d = reflect a (vbound i)
                                      in Lam a (reify b (f d) (i+1))
reify (a :*: b) (VPair v1 v2) = Pair <$> reify a v1 <*> reify b v2
reify (T a)     (VMonad m)    = reifyVMonad a m

reifyVMonad :: Type -> VMonad Value -> TermFam
reifyVMonad a (VReturn v)   = Return <$> reify a v
reifyVMonad a (VBind t e k) = \i -> let d = reflect t (vbound i)
                                    in Bind (e i) (reifyVMonad a (k d) (i+1))

reflect :: Type -> TermFam -> Value
reflect B         t = VNeutral t
reflect (a :=> b) t = VLam $ \v -> reflect b (App <$> t <*> reify a v)
reflect (a :*: b) t = VPair (reflect a (Fst <$> t)) (reflect b (Snd <$> t))
reflect (T a)     t = VMonad (VBind a t VReturn)

normalise :: Term -> Type -> Term
normalise tm ty = reify ty (eval tm []) 0

--------------------------------------------------------------------------------
tm1 = Lam (B :=> B) (Var 0)
ty1 = (B :=> B) :=> (B :=> B)

tm2 = Lam (T B :=> T B) (Var 0)
ty2 = (T B :=> T B) :=> (T B :=> T B)

tm3 = Lam (T B) (Var 0)
ty3 = T B :=> T B

tm4 = Lam (T B) (Bind (Bind (Var 0) (Var 1)) (Var 1))
ty4 = T B :=> T B