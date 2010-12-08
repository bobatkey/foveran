module Data.BooleanAlgebra where

class BooleanAlgebra a where
    (.&.)      :: a -> a -> a
    (.|.)      :: a -> a -> a
    complement :: a -> a
    one        :: a
    zero       :: a

instance BooleanAlgebra Bool where
    (.&.)      = (&&)
    (.|.)      = (||)
    complement = not
    one        = True
    zero       = False

prop_or_assoc a b c     = a .|. (b .|. c) == (a .|. b) .|. c
prop_or_commutative a b = a .|. b == b .|. a

prop_and_assoc a b c     = a .&. (b .&. c) == (a .&. b) .&. c
prop_and_commutative a b = a .&. b == b .&. a

prop_distrib1 a b c = a .|. (b .&. c) == (a .|. b) .&. (a .|. c)
prop_distrib2 a b c = a .&. (b .|. c) == (a .&. b) .|. (a .&. c)

prop_absorb1 a b = a .|. (a .&. b) == a
prop_absorb2 a b = a .&. (a .|. b) == a

prop_complement1 a = a .&. complement a == zero
prop_complement2 a = a .|. complement a == one

