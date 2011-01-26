module DelayIdiomNBE where

-- Terms are only properly well-typed if they correctly respect the
-- clock discipline, but this doesn't show up here yet. Think of it as
-- a Curry-style system over the STLC system here.

import Text.Show.Functions
import Control.Applicative

data Type
    = B | Type :=> Type | De Type | Type :*: Type
    deriving (Eq, Show)

infixr 5 :=>
infixr 6 :*:

data Term
    = Var   Int
    | Free  Type String
    | Lam   Type Term
    | App   Term Term
    | Pure  Term
    | Ap    Term Term
    | Pair  Term Term
    | Fst   Term
    | Snd   Term
    | Let   Type Term Term
    | Fix   Term
    | Force Type Term
    deriving Show

type TermFam = Int -> Term

data Value
    = VLam     (Value -> Value)
    | VPair    Value Value
    | VNeutral TermFam
    | VIdiom   (VIdiom TermFam)
    deriving Show

data VIdiom a
    = Stop a
    | Step Type (Int -> Term) (VIdiom (TermFam -> a))
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

-- FIXME: replace the Lets here with proper substitution. This would
-- match the equational theory I have in my head, and also give
-- smaller terms in many cases because most stuff would be thrown
-- away.
vpure :: Term -> [(Type, Value)] -> Value
vpure t env = VIdiom (Stop (suspension env (const t)))
    where suspension []           t = t
          suspension ((ty,v):env) t = suspension env (\i -> Let ty (reify ty v i) (t (i+1)))

tmApp :: TermFam -> TermFam -> TermFam
tmApp t1 t2 = App <$> t1 <*> t2

tmLam :: Type -> (TermFam -> TermFam) -> TermFam
tmLam a f = \i -> Lam a (f (vbound i) (i+1))

vap :: Value -> Value -> Value
vap (VIdiom f) (VIdiom a) = VIdiom ((tmApp <$> f) <*> a)

vfst :: Value -> Value
vfst (VPair v _) = v

vsnd :: Value -> Value
vsnd (VPair _ v) = v

vforce :: Type -> [(Type,Value)] -> Value -> Value
vforce ty env (VIdiom (Stop t)) = eval (t (length env)) env
vforce ty env (VIdiom k)        = reflect ty (Force ty <$> reifyIdiom ty k)

--------------------------------------------------------------------------------
eval :: Term -> [(Type,Value)] -> Value
eval (Var i)        = \env -> snd (env !! i)
eval (Free ty nm)   = pure (reflect ty (pure $ Free ty nm))
eval (Lam ty t)     = \env -> VLam $ \v -> eval t ((ty,v):env)
eval (App t1 t2)    = ($$) <$> eval t1 <*> eval t2
eval (Pure t)       = vpure t
eval (Ap t1 t2)     = vap <$> eval t1 <*> eval t2
eval (Pair t1 t2)   = VPair <$> eval t1 <*> eval t2
eval (Fst t)        = vfst <$> eval t
eval (Snd t)        = vsnd <$> eval t
eval (Let ty t1 t2) = \env -> eval t2 ((ty, eval t1 env):env)
eval (Fix t)        = ($$) <$> eval t <*> vpure (Fix t)
eval (Force ty t)   = vforce ty <*> eval t

vbound :: Int -> TermFam
vbound i j = Var (j - i - 1)

reify :: Type -> Value -> TermFam
reify B         (VNeutral t)  = t
reify (a :=> b) (VLam f)      = \i -> let d = reflect a (vbound i)
                                      in Lam a (reify b (f d) (i + 1))
reify (De a)    (VIdiom c)    = reifyIdiom a c
reify (a :*: b) (VPair v1 v2) = Pair <$> reify a v1 <*> reify b v2
reify t         v             = error $ "bad reify: " ++ show t ++ " on " ++ show v

reifyIdiom a (Stop t)     = Pure <$> t
reifyIdiom a (Step b t k) = Ap <$> reifyIdiom (b :=> a) (tmLam b <$> k) <*> t

reflect :: Type -> TermFam -> Value
reflect (a :=> b) t = VLam $ \v -> reflect b (App <$> t <*> reify a v)
reflect B         t = VNeutral t
reflect (De a)    t = VIdiom (Step a t $ Stop id)
reflect (a :*: b) t = VPair (reflect a (Fst <$> t)) (reflect b (Snd <$> t))

normalise :: Term -> Type -> Term
normalise tm ty = reify ty (eval tm []) 0

--------------------------------------------------------------------------------
tm0 = Lam (B :=> B :=> B) $ Lam (De B) $ Pure (Var 1) `Ap` Var 0 `Ap` Var 0
ty0 = (B :=> B :=> B) :=> De B :=> De B

tm1 = Lam (B :=> B) (Var 0)
ty1 = (B :=> B) :=> B :=> B

tm2 = Lam (B :=> B) (Lam B (Pure (Var 1 `App` Var 0)))
ty2 = (B :=> B) :=> B :=> De B

tm3 = Lam (B :=> B) (Lam B (Force B (Pure (Var 1 `App` Var 0))))
ty3 = (B :=> B) :=> B :=> B

tm4 = Lam (De (B :=> B)) (Force (B :=> B) (Var 0))
ty4 = De (B :=> B) :=> B :=> B

tm5 = tm4 `App` (Pure (Lam B (Var 0)))
ty5 = B :=> B

tm6 = Lam B (minTm `App` Var 0 `App` ((Lam B (Var 0)) `App` Var 0))
ty6 = B :=> B

tm7 = Lam B $ Pure (Lam B (Var 0)) `Ap` Pure (Var 0)
ty7 = B :=> De B

tm8 = Lam B $ Force B (tm7 `App` Var 0)
ty8 = B :=> B

--------------------------------------------------------------------------------
-- example replacing each number in a pair with its minimum, in a
-- convoluted way.
minTm = Free (B :=> B :=> B) "min"

fstFunc = Lam (B :*: B) (Fst (Var 0))

replaceTy = De ((B :*: B) :=> (B :*: (De B :*: De B))) :=>
                (B :*: B) :=> (B :*: (De B :*: De B))
replaceTm =
    Lam (De ((B :*: B) :=> (B :*: (De B :*: De B)))) $
    Lam (B :*: B) $
    Pair (minTm `App` (Fst (Var 0)) `App` (Snd (Var 0)))
         (Pair (Pure fstFunc `Ap` (Var 1 `Ap` Pure (Var 0)))
               (Pure fstFunc `Ap` (Var 1 `Ap` Pure (Var 0))))

replaceMinTm = Lam (B :*: B) (Snd (Fix replaceTm `App` Var 0))
replaceMinTy = (B :*: B) :=> (De B :*: De B)

xTm = Lam (B :*: B) (Force B (Fst (replaceMinTm `App` Var 0)))
xTy = (B :*: B) :=> B
