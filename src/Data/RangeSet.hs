{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}

-- |
-- Module      :  Data.RangeSet
-- Copyright   :  Robert Atkey 2010
-- License     :  BSD3
--
-- Maintainer  :  bob.atkey@gmail.com
-- Stability   :  experimental
-- Portability :  unknown
--
-- Representation of sets of elements of 'Bounded' instances. Such
-- types have a total ordering with minimum and maximum elements. Sets
-- are represented as ranges of elements.

-- Representation of unicode character sets, based on cset.ml from
-- Alain Frisch's ulex for ocaml. One difference is that because we
-- are using 'Char's to represent characters, the implementation has
-- to be more careful about going off the end of the range of
-- expressible characters.

module Data.RangeSet
    (
      -- * Range Set type
      Set ()
      
    -- * Construction 
    , singleton
    , interval
      
    -- * Queries
    , memberOf
    , getRepresentative
    , null
    , ranges)
    where

import Prelude hiding (null)
import Data.List (intercalate)
import Data.String
import Data.BooleanAlgebra
import Data.Functor
import Test.QuickCheck hiding (ranges)

{- Representation of character sets, copied from cset.ml from Alain
   Frisch's ulex for ocaml. Only difference is that because we are
   using 'Char's to represent characters, the implementation has to be
   more careful about going off the end of the range of expressible
   characters. -}

{- Character sets are represented as increasing, non-overlapping,
   non-empty lists of intervals -}

-- TODO: coalescing of ranges that abutt. Seems to do this already?

-- | A set of unicode codepoints. Note that this type is an instance
-- of 'IsString', so character sets can be specified as literal
-- strings.
newtype Set a = Set { unSet :: [(a,a)] }
    deriving (Eq,Ord)

isNormalForm :: Ord a => Set a -> Bool
isNormalForm (Set l) = check1 l
    where
      check1 []        = True
      check1 ((a,b):l) = a <= b && check b l
          
      check x []        = True
      check x ((a,b):l) = x < a && a <= b && check b l

-- FIXME: this sucks, would be (slightly) better to generate a list of
-- ranges and then union them
instance (Ord a, Arbitrary a) => Arbitrary (Set a) where
    arbitrary = (Set <$> arbitrary) `suchThat` isNormalForm

instance (Enum a, Ord a, Bounded a) => BooleanAlgebra (Set a) where
    (.&.)      = intersect
    (.|.)      = union
    complement = Data.RangeSet.complement
    one        = everything
    zero       = empty

-- | Returns the list of ranges of unicode codepoints represented by
-- the given 'CSet'. The end points of each range are inclusive, and
-- the ranges are in increasing order.
ranges :: Set a -> [(a,a)]
ranges (Set l) = l

instance (Eq a, Show a) => Show (Set a) where
    show (Set l) = "[" ++ intercalate "," (map showRange l) ++ "]"
        where showRange (l,h)
                  | l == h    = show l
                  | otherwise = show l ++ "-" ++ show h

-- | The empty set
empty :: Set a
empty = Set []

-- FIXME: could shortcut search if i > c.
-- | Test to determine whether the given 'a' is in the 'Set a'.
memberOf :: Ord a => a -> Set a -> Bool
memberOf c (Set l) = aux c l
    where
      aux c []        = False
      aux c ((i,j):l) = (i <= c && c <= j) || aux c l

-- | Returns an arbitrary character in the given set. Returns
-- 'Nothing' if the set is empty.
getRepresentative :: Set a -> Maybe a
getRepresentative (Set [])        = Nothing
getRepresentative (Set ((i,_):_)) = Just i

-- | Set consisting of a single unicode code point.
singleton :: a -> Set a
singleton c = Set [(c,c)]

-- | Test to determine whether the given character set is empty.
null :: Set a -> Bool
null (Set []) = True
null (Set _)  = False

-- | Sets containing all the characters between the two given
-- endpoints, inclusive of these points. The arguments need not be in
-- any particular order.
interval :: Ord a => a -> a -> Set a
interval i j = Set $ if i <= j then [(i,j)] else [(j,i)]

-- | The set containing all of the elements of 'a'
everything :: (Ord a, Bounded a) => Set a
everything = interval minBound maxBound

-- | Computes the union of two character sets, i.e. the set with all
-- the characters contained in the two arguments.
union :: (Enum a, Bounded a, Ord a) => Set a -> Set a -> Set a
union (Set c1) (Set c2) = Set $ aux c1 c2
    where
      aux [] c2 = c2
      aux c1 [] = c1
      aux c1@((i1,j1):r1) c2@((i2,j2):r2) =
          if i1 <= i2 then
              if j1 /= maxBound && succ j1 < i2 then (i1,j1):aux r1 c2
              else if j1 < j2 then aux r1 ((i1,j2):r2)
                   else aux c1 r2
          else aux c2 c1

-- | Computes the complement of the given set, i.e. the set of all
-- characters not in the argument.
complement :: (Enum a, Bounded a, Ord a) => Set a -> Set a
complement = Set . aux minBound . unSet
    where
      aux start []      
          | start <= maxBound = [(start,maxBound)]
          | otherwise         = []
      aux start ((i,j):l)
          | start == i        = if j == maxBound then [] else aux (succ j) l
          | otherwise         = (start,pred i):if j == maxBound then [] else aux (succ j) l

-- | Computes the intersection of two sets. Returns the set containing
-- all the elements found in both of the given sets.
intersect :: (Enum a, Bounded a, Ord a) => Set a -> Set a -> Set a
intersect c1 c2 = Data.RangeSet.complement (Data.RangeSet.complement c1 `union` Data.RangeSet.complement c2)

{------------------------------------------------------------------------------}
prop_interval a b c = a <= c && c <= b ==> c `memberOf` (interval a b)

{-
{------------------------------------------------------------------------------}
-- Some character sets
-- FIXME: split this out?
xmlNameStartChar = singleton ':'
                   `union`
                   interval 'A' 'Z'
                   `union`
                   singleton '_'
                   `union`
                   interval 'a' 'z'
                   `union`
                   interval '\xc0' '\xd6'
                   `union`
                   interval '\xd8' '\xf6'
                   `union`
                   interval '\x370' '\x37d'
                   `union`
                   interval '\x37f' '\x1fff'
                   `union`
                   interval '\x200c' '\x200d'
                   `union`
                   interval '\x2070' '\x218f'
                   `union`
                   interval '\x2c00' '\x2fef'
                   `union`
                   interval '\x3001' '\xd7ff'
                   `union`
                   interval '\xf900' '\xFDCF'
                   `union`
                   interval '\xfdf0' '\xfffd'
                   `union`
                   interval '\x10000' '\xeffff'

xmlNameChar  = xmlNameStartChar
               `union`
               singleton '-'
               `union`
--               singleton '.'
--               `union`
               interval '0' '9'
               `union`
               singleton '\xb7'
               `union`
               interval '\x0300' '\x036f'
               `union`
               interval '\x203f' '\x2040'

mathematicalOperators = interval '\x2200' '\x22ff'

nameStartChar = xmlNameStartChar `union` mathematicalOperators
nameChar = xmlNameChar `union` mathematicalOperators `union` singleton '\''

num = interval '0' '9'

space :: Set Char
space = " \n\t"
-}