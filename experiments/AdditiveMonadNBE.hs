module AdditiveMonadNBE where

{-
Guards

guard :: Bool -> T U

commutes with everything:
  guard M >> N == N >>= \x. guard M >> return x

so the normal form puts them all at the end (and ands them?)

  guard M >> guard N == guard (M && N)

  don't normalise boolean expressions.
-}

{-
Recursion:
- Add a letrec, don't normalise
- (Also add a let)
-}

{-
Negation
- An operator negate : T B -> T B
- Bubble negates up to the top? What about unions?
negate M `mplus` negate N == 

(not A) or (not B) = not ((not (not A)) and (not (not B))) = not (A and B)

- implement 'and' by 

- or only negate let-bound variables?
-}

-- FIXME: What about the IF-RECORD rule in Ezra's paper? This is
-- separate to guards.

import Text.Show.Functions
import Control.Applicative
import Control.Monad

data Type
    = B | Type :=> Type | Type :*: Type | T Type | U | Bool
    deriving (Eq, Show)

infixr 5 :=>
infixr 6 :*:

data Term
    = Var  Int
    | Unit
    | Free Type String
    | Lam  Type Term
    | App  Term Term
    | Pair Term Term
    | Fst  Term
    | Snd  Term
    | Return Term
    | Bind   Term Term
    | MZero
    | MPlus  Term Term
    deriving (Eq, Show)

type TermFam = Int -> Term

data Value
    = VLam     (Value -> Value)
    | VUnit
    | VPair    Value Value
    | VNeutral TermFam
    | VMonad   (VAdditiveMonad Value)
    deriving Show

data VMonad a
    = VReturn a
    | VBind   Type TermFam (Value -> VMonad a)
    deriving Show

instance Monad VMonad where
    return = VReturn
    VReturn a   >>= f = f a
    VBind t e k >>= f = VBind t e (\v -> k v >>= f)

newtype VAdditiveMonad a =
    VAM { unVAM :: [VMonad a] }
    deriving Show

unSequence :: VMonad [a] -> [VMonad a]
unSequence (VReturn l)   = map VReturn l
unSequence (VBind t e k) = [ VBind t e (\v -> k' v !! j) | j <- [0..n-1] ]
    where
      k' = unSequence . k
      n  = length (k' undefined)

instance Monad VAdditiveMonad where
    return a    = VAM [return a]
    VAM l >>= f = VAM $ map join $ concat $ map (unSequence . liftM (unVAM . f)) l

instance MonadPlus VAdditiveMonad where
    mzero       = VAM []
    x `mplus` y = VAM $ unVAM x ++ unVAM y

--------------------------------------------------------------------------------
($$) :: Value -> Value -> Value
VLam f $$ v = f v

vfst :: Value -> Value
vfst (VPair v _) = v

vsnd :: Value -> Value
vsnd (VPair _ v) = v

vreturn :: Value -> Value
vreturn = VMonad . return

unVMonad (VMonad vm) = vm

vbind v f = VMonad $ unVMonad v >>= unVMonad . f

--------------------------------------------------------------------------------
eval :: Term -> [Value] -> Value
eval (Var i)       = \env -> env !! i
eval Unit          = pure VUnit
eval (Free ty nm)  = pure (reflect ty (pure $ Free ty nm))
eval (Lam ty t)    = \env -> VLam $ \v -> eval t (v:env)
eval (App t1 t2)   = ($$)    <$> eval t1 <*> eval t2
eval (Pair t1 t2)  = VPair   <$> eval t1 <*> eval t2
eval (Fst t)       = vfst    <$> eval t
eval (Snd t)       = vsnd    <$> eval t
eval (Return t)    = vreturn <$> eval t
eval (Bind t1 t2)  = vbind   <$> eval t1 <*> (\env v -> eval t2 (v:env))
eval MZero         = pure (VMonad mzero)
eval (MPlus t1 t2) = VMonad <$> (mplus <$> (unVMonad <$> eval t1) <*> (unVMonad <$> eval t2))

vbound :: Int -> TermFam
vbound i j = Var (j - i - 1)

reify :: Type -> Value -> TermFam
reify B         (VNeutral t)     = t
reify U         VUnit            = pure Unit
reify (a :=> b) (VLam f)         = \i -> let d = reflect a (vbound i)
                                         in Lam a (reify b (f d) (i+1))
reify (a :*: b) (VPair v1 v2)    = Pair <$> reify a v1 <*> reify b v2
reify (T a)     (VMonad (VAM m)) = reifyVAM a m

reifyVAM :: Type -> [VMonad Value] -> TermFam
reifyVAM a []    = \i -> MZero
reifyVAM a (m:l) = MPlus <$> reifyVMonad a m <*> reifyVAM a l

reifyVMonad :: Type -> VMonad Value -> TermFam
reifyVMonad a (VReturn v)   = Return <$> reify a v
reifyVMonad a (VBind t e k) = \i -> let d = reflect t (vbound i)
                                    in Bind (e i) (reifyVMonad a (k d) (i+1))

reflect :: Type -> TermFam -> Value
reflect B         t = VNeutral t
reflect U         t = VUnit
reflect (a :=> b) t = VLam $ \v -> reflect b (App <$> t <*> reify a v)
reflect (a :*: b) t = VPair (reflect a (Fst <$> t)) (reflect b (Snd <$> t))
reflect (T a)     t = VMonad (VAM [VBind a t VReturn])

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

tm5 = Lam (T B) (Bind (Var 0) (MPlus (Bind (Var 1) (Return (Var 0)))
                                     (Return (Var 0))))
ty5 = T B :=> T B
