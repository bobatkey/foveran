{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      :  Data.BooleanAlgebra
-- Copyright   :  (C) Robert Atkey 2013
-- License     :  BSD3
--
-- Maintainer  :  bob.atkey@gmail.com
-- Stability   :  experimental
-- Portability :  unknown
--
-- Boolean algebras as a type class.

module Data.BooleanAlgebra
    ( -- * Boolean Algebra class
      BooleanAlgebra (..)

    -- * Conjunction
    , Conjunctive (..)
    , and
    , all

    -- * Disjunction
    , Disjunctive (..)
    , or
    , any
    , unions
    , unionsWith

    -- * Required properties
    , prop_or_assoc
    , prop_or_commutative
    , prop_and_assoc
    , prop_and_commutative
    , prop_distrib1
    , prop_distrib2
    , prop_absorb1
    , prop_absorb2
    , prop_complement1
    , prop_complement2
    )
    where

import Prelude hiding (and, all, or, any)

-- | Boolean algebras.
class BooleanAlgebra a where
    -- | Conjunction, lattice meet, logical and.
    (.&.)      :: a -> a -> a

    -- | Disjunction, lattice join, logical or.
    (.|.)      :: a -> a -> a

    -- | Top element ("Truth")
    one        :: a

    -- | Bottom element ("False")
    zero       :: a

    -- | Complementation ("not")
    complement :: a -> a

-- | Archetypal instance of a boolean algebra.
instance BooleanAlgebra Bool where
    (.&.)      = (&&)
    (.|.)      = (||)
    complement = not
    one        = True
    zero       = False

{-
-- | Lifting of boolean algebras up to applicative functors. Doesn't
-- work due to problems with overlapping instances.
instance (Applicative f, BooleanAlgebra ba) => BooleanAlgebra (f ba) where
    (.&.) = liftA2 (.&.)
    (.|.) = liftA2 (.|.)
    complement = liftA complement
    one = pure one
    zero = pure zero
-}

--------------------------------------------------------------------------------
-- | Newtype marker used to access the conjunctive structure of a
-- boolean algebra.
newtype Conjunctive a = Conjunctive { fromConjunctive :: a }

-- | Treat the conjunctive structure of a boolean algebra as a monoid.
instance BooleanAlgebra a => Monoid (Conjunctive a) where
    mempty = Conjunctive one
    mappend (Conjunctive x) (Conjunctive y) = Conjunctive (x .&. y)

-- | Use the '(.&.)' operation from a 'BooleanAlgebra' to combine all
-- the elements of a 'Data.Foldable.Foldable' container type,
-- effectively and-ing all the elements together. This function
-- generalises the 'Prelude.and' and 'Data.Foldable.and' functions to
-- work for any 'Data.Foldable.Foldable' instance, and any
-- 'BooleanAlgebra' instance.
and :: (BooleanAlgebra a, Foldable t) => t a -> a
and = fromConjunctive . foldMap Conjunctive

-- | Map each element of a 'Data.Foldable.Foldable' container type to
-- a 'BooleanAlgebra' and combine them using '(.&.)'. This function
-- generalises the 'Prelude.all' and 'Data.Foldable.all' functions to
-- work for any 'Data.Foldable.Foldable' container, and any
-- 'BooleanAlgebra'.
all :: (BooleanAlgebra b, Foldable t) => (a -> b) -> t a -> b
all f = fromConjunctive . foldMap (Conjunctive . f)

--------------------------------------------------------------------------------
-- | Newtype marker used to access the disjunctive structure of a
-- boolean algebra.
newtype Disjunctive a = Disjunctive { fromDisjunctive :: a }

-- | Treat the disjunctive structure of a boolean algebra as a monoid.
instance BooleanAlgebra a => Monoid (Disjunctive a) where
    mempty = Disjunctive zero
    mappend (Disjunctive x) (Disjunctive y) = Disjunctive (x .|. y)

-- | Use the '(.|.)' operation from a 'BooleanAlgebra' to combine all
-- the elements of a 'Data.Foldable.Foldable' container type,
-- effectively or-ing all the elements together. This function
-- generalises the 'Prelude.or' and 'Data.Foldable.or' functions to
-- work for any 'Data.Foldable.Foldable' container, and any
-- 'BooleanAlgebra'.
or :: (BooleanAlgebra a, Foldable t) => t a -> a
or = fromDisjunctive . foldMap Disjunctive

-- | Map each element of a 'Data.Foldable.Foldable' container type to
-- a 'BooleanAlgebra' and combine them using '(.|.)'. This function
-- generalises the 'Prelude.any' and 'Data.Foldable.any' functions to
-- work for any 'Data.Foldable.Foldable' container, and any
-- 'BooleanAlgebra'.
any :: (BooleanAlgebra b, Foldable t) => (a -> b) -> t a -> b
any f = fromDisjunctive . foldMap (Disjunctive . f)

unionsWith :: (BooleanAlgebra b, Foldable t) => (a -> b) -> t a -> b
unionsWith = any

unions :: (BooleanAlgebra b, Foldable t) => t b -> b
unions = or

--------------------------------------------------------------------------------
-- | Property: @forall a b c. a .|. (b .|. c) == (a .|. b) .|. c@
prop_or_assoc :: (BooleanAlgebra a, Eq a) => a -> a -> a -> Bool
prop_or_assoc a b c     = a .|. (b .|. c) == (a .|. b) .|. c

-- | Property: @forall a b. a .|. b == b .|. a@
prop_or_commutative :: (BooleanAlgebra a, Eq a) => a -> a -> Bool
prop_or_commutative a b = a .|. b == b .|. a

-- | Property: @forall a b c. a .&. (b .&. c) == (a .&. b) .&. c@
prop_and_assoc :: (BooleanAlgebra a, Eq a) => a -> a -> a -> Bool
prop_and_assoc a b c     = a .&. (b .&. c) == (a .&. b) .&. c

-- | Property: @forall a b. a .&. b == b .&. a@
prop_and_commutative :: (BooleanAlgebra a, Eq a) => a -> a -> Bool
prop_and_commutative a b = a .&. b == b .&. a

-- | Property: @forall a b c. a .|. (b .&. c) == (a .|. b) .&. (a .|. c)@
prop_distrib1 :: (BooleanAlgebra a, Eq a) => a -> a -> a -> Bool
prop_distrib1 a b c = a .|. (b .&. c) == (a .|. b) .&. (a .|. c)

-- | Property: @forall a b c. a .&. (b .|. c) == (a .&. b) .|. (a .&. c)@
prop_distrib2 :: (BooleanAlgebra a, Eq a) => a -> a -> a -> Bool
prop_distrib2 a b c = a .&. (b .|. c) == (a .&. b) .|. (a .&. c)

-- | Property: @forall a b. a .|. (a .&. b) == a@
prop_absorb1 :: (BooleanAlgebra a, Eq a) => a -> a -> Bool
prop_absorb1 a b = a .|. (a .&. b) == a

-- | Property: @forall a b. a .&. (a .|. b) == a@
prop_absorb2 :: (BooleanAlgebra a, Eq a) => a -> a -> Bool
prop_absorb2 a b = a .&. (a .|. b) == a

-- | Property: @forall a. a .&. complement a == zero@
prop_complement1 :: (BooleanAlgebra a, Eq a) => a -> Bool
prop_complement1 a = a .&. complement a == zero

-- | Property: @forall a. a .|. complement a == one@
prop_complement2 :: (BooleanAlgebra a, Eq a) => a -> Bool
prop_complement2 a = a .|. complement a == one
