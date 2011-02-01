module MonoidNBE where

import Text.Show.Functions
import Control.Applicative

data Type
    = B | Type :=> Type | Type :*: Type
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
    | MUnit
    | MAppend Term Term
    deriving (Eq, Show)

type TermFam = Int -> Term

data Value
    = VLam     (Value -> Value)
    | VPair    Value Value
    | VMonoid  [TermFam]
--    | VNeutral TermFam
    deriving Show

--------------------------------------------------------------------------------
($$) :: Value -> Value -> Value
VLam f $$ v = f v

vfst :: Value -> Value
vfst (VPair v _) = v

vsnd :: Value -> Value
vsnd (VPair _ v) = v

vMunit :: Value
vMunit = VMonoid []

vMappend :: Value -> Value -> Value
vMappend (VMonoid a) (VMonoid b) = VMonoid (a ++ b)

--------------------------------------------------------------------------------
eval :: Term -> [(Type,Value)] -> Value
eval (Var i) = \env -> snd (env !! i)
eval (Free ty nm)    = pure (reflect ty (pure $ Free ty nm))
eval (Lam ty t)      = \env -> VLam $ \v -> eval t ((ty,v):env)
eval (App t1 t2)     = ($$) <$> eval t1 <*> eval t2
eval (Pair t1 t2)    = VPair <$> eval t1 <*> eval t2
eval (Fst t)         = vfst <$> eval t
eval (Snd t)         = vsnd <$> eval t
eval MUnit           = pure vMunit
eval (MAppend t1 t2) = vMappend <$> eval t1 <*> eval t2

vbound :: Int -> TermFam
vbound i j = Var (j - i - 1)

reify :: Type -> Value -> TermFam
reify B         (VMonoid t)   = \i -> foldr MAppend MUnit $ map ($ i) t
reify (a :=> b) (VLam f)      = \i -> let d = reflect a (vbound i)
                                      in Lam a (reify b (f d) (i+1))
reify (a :*: b) (VPair v1 v2) = Pair <$> reify a v1 <*> reify b v2

reflect :: Type -> TermFam -> Value
reflect B         t = VMonoid [t]
reflect (a :=> b) t = VLam $ \v -> reflect b (App <$> t <*> reify a v)
reflect (a :*: b) t = VPair (reflect a (Fst <$> t)) (reflect b (Snd <$> t))

normalise :: Term -> Type -> Term
normalise tm ty = reify ty (eval tm []) 0

--------------------------------------------------------------------------------
tm1 = Lam (B :=> B) (Var 0)
ty1 = (B :=> B) :=> (B :=> B)

-- Bracketing is futile, you will be associated
tm2 = Lam B ((Var 0 `MAppend` Var 0) `MAppend` Var 0)
ty2 = B :=> B

tm3 = Lam B (Var 0 `MAppend` (Var 0 `MAppend` Var 0))
ty3 = B :=> B

--
tm4 = Lam B $ Lam B $ Var 0 `MAppend` Var 1
ty4 = B :=> B :=> B

tm5 = Lam B $ Var 0 `MAppend` MUnit `MAppend` Var 0
ty5 = B :=> B

tm6 = Lam B $ Var 0 `MAppend` Var 0
ty6 = B :=> B

{- Now, it would be good if we could also have a monoid morphism from
B to 'C -> C' that was understood to be so by the NBE stuff.

a) need some special 'B' values that translate to certain combinators
(need some ops on 'C' for this to work)

b) MUnit must convert to the identity

c) MAppend must convert to function composition

I guess that there should be a semantic function that takes in the
lists of 'B' values and basically maps them to 'C -> C' values, using
(semantic) composition.

-}