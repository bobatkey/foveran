{-# LANGUAGE OverloadedStrings, FlexibleInstances, TupleSections, DeriveFunctor #-}

-- |
-- Module      :  Data.RangeSet
-- Copyright   :  (C) Robert Atkey 2013
-- License     :  BSD3
--
-- Maintainer  :  bob.atkey@gmail.com
-- Stability   :  experimental
-- Portability :  unknown
--
-- Representation of sets of elements of ('Bounded', 'Ord', 'Enum')
-- instances. Such types have a total ordering with minimum and
-- maximum elements. Sets are represented as ranges of elements.
--
-- The implementation is based on the implementation of sets of
-- Unicode code points in cset.ml from Alain Frisch's ulex for
-- OCaml. One difference is that because this implementation uses
-- instances of 'Bounded' to represent characters, it has to be more
-- careful about going off the end of the range.

module Data.RangeSet
    (
    -- * Subsets of 'Bounded' types
      Set ()
      
    -- ** Construction 
    , singleton
    , interval
      
    -- ** Queries
    , member
    , getRepresentative
    , null
    , ranges
    
    -- * Partitions of 'Bounded' types
    , Partition
    , fromSet
      
    -- * Total maps
    , TotalMap
    , makeTotalMap
    , makeTotalMapA
    , ($@)
    , assocs
    , domainPartition
    )
    where

import           Prelude hiding (null)
import qualified Data.Set as S
import           Data.List (intercalate)
import           Data.Maybe (fromJust)
import           Data.BooleanAlgebra

-- | A subset of the given type. Stored as a list of ranges.
newtype Set a = Set { unSet :: [(a,a)] }
    deriving (Eq,Ord)

_isNormalForm :: Ord a => Set a -> Bool
_isNormalForm (Set l) = check1 l
    where
      check1 []        = True
      check1 ((a,b):l) = a <= b && check b l
          
      check x []        = True
      check x ((a,b):l) = x < a && a <= b && check b l

-- FIXME: this sucks, would be (slightly) better to generate a list of
-- ranges and then union them
--instance (Ord a, Arbitrary a) => Arbitrary (Set a) where
--    arbitrary = (Set <$> arbitrary) `suchThat` isNormalForm

-- | 'Data.RangeSet.Set's over bounded types are 'BooleanAlgebra's
-- using the normal set-theoretic operations.
instance (Enum a, Ord a, Bounded a) => BooleanAlgebra (Set a) where
    (.&.)      = intersect
    (.|.)      = union
    complement = Data.RangeSet.complement
    one        = everything
    zero       = empty

-- | Returns the list of ranges of elements represented by the given
-- 'Set'. The end points of each range are inclusive, and the ranges
-- are in increasing order.
ranges :: Set a -> [(a,a)]
ranges (Set l) = l

-- | String representation of 'Data.RangeSet.Set's as an ordered list
-- of ranges. See also 'ranges'.
instance (Eq a, Show a) => Show (Set a) where
    show (Set l) = "[" ++ intercalate "," (map showRange l) ++ "]"
        where showRange (l,h)
                  | l == h    = show l
                  | otherwise = show l ++ "-" ++ show h

-- | The empty set. A synonym for 'zero'.
empty :: Set a
empty = Set []

-- | Test to determine whether the given @a@ is in the 'Set'.
member :: Ord a => a -> Set a -> Bool
member c (Set l) = aux c l
    where
      -- FIXME: could shortcut search if i > c.
      aux c []        = False
      aux c ((i,j):l) = (i <= c && c <= j) || aux c l

-- | Returns an arbitrary element in the given 'Set'. Returns
-- 'Nothing' if the set is empty.
getRepresentative :: Set a -> Maybe a
getRepresentative (Set [])        = Nothing
getRepresentative (Set ((i,_):_)) = Just i

-- | 'Set' consisting of a element.
singleton :: a -> Set a
singleton c = Set [(c,c)]

-- | Test to determine whether the given set is empty.
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
-- elements not in the given set.
complement :: (Enum a, Bounded a, Ord a) => Set a -> Set a
complement = Set . aux minBound . unSet
    where
      aux start []      
          | start <= maxBound = [(start,maxBound)]
          | otherwise         = []
      aux start ((i,j):l)
          | start == i =
              if j == maxBound then [] else aux (succ j) l
          | otherwise =
              (start,pred i):if j == maxBound then [] else aux (succ j) l

-- | Computes the intersection of two sets. Returns the set containing
-- all the elements found in both of the given sets.
intersect :: (Enum a, Bounded a, Ord a) => Set a -> Set a -> Set a
intersect c1 c2 =
    Data.RangeSet.complement
        (Data.RangeSet.complement c1 `union` Data.RangeSet.complement c2)

--------------------------------------------------------------------------------
-- | A partition of a 'Bounded' type into equivalence classes.
newtype Partition a = Partition (S.Set (Set a))
    deriving Show

-- | Creates a partition with two equivalence classes. One class is
-- the given set, and the other is its complement.
fromSet :: (Enum a, Bounded a, Ord a) => Set a -> Partition a
fromSet s 
    | s == everything = Partition (S.fromList [ s ])
    | s == empty      = Partition (S.fromList [ everything ])
    | otherwise       = Partition (S.fromList [ s, Data.RangeSet.complement s ])

-- | Intersection of partitions. FIXME: should be a lattice.
instance (Enum a, Bounded a, Ord a) => Monoid (Partition a) where
    mempty = Partition (S.fromList [ everything ])
    mappend (Partition x) (Partition y) =
        Partition $ S.fromList [ i |
                                 a <- S.elems x
                               , b <- S.elems y
                               , let i = a `intersect` b 
                               , not (null i)] 

--------------------------------------------------------------------------------
-- FIXME: need a better representation than this Should be a balanced
-- tree. Also the Eq/Ord instances should equate extensionally equal
-- total maps.

-- | A total map from @a@ to @b@, represented using a partition of the
-- domain into equivalence classes.
newtype TotalMap a b = TotalMap { unTotalMap :: [(Set a,b)] }
    deriving (Eq, Ord, Show, Functor)

-- | Construct a 'TotalMap' by providing a function to 
makeTotalMap :: (a -> b)
             -> Partition a
             -> TotalMap a b
makeTotalMap f (Partition sets) =
    TotalMap [ (set, f (fromJust $ getRepresentative set)) | set <- S.elems sets ]

-- | 'Applicative' version of 'makeTotalMap'.
makeTotalMapA :: Applicative f =>
                 (a -> f b)
              -> Partition a
              -> f (TotalMap a b)
makeTotalMapA f (Partition sets) =
    TotalMap <$> (traverse doClass $ S.elems sets)
    where
      doClass cls = (cls,) <$> f (fromJust $ getRepresentative cls)

-- FIXME: this is the wrong name

-- | Return the 'Partition' of @a@ that was used to construct this
-- 'TotalMap'. Note that this may not necessarily be the coarsest
-- partition of the domain of this 'TotalMap'.
domainPartition :: Ord a => TotalMap a b -> Partition a
domainPartition = Partition . S.fromList . map fst . unTotalMap

-- | Apply a 'TotalMap' to a value.
($@) :: Ord a => TotalMap a b -> a -> b
TotalMap mappings $@ a = go mappings
    where
      go []        = error "internal error: not a total map"
      go ((s,b):m) = if a `member` s then b else go m

-- | Returns the list of equivalence classes over the domain and their
-- associated codomain values.
assocs :: TotalMap a b -> [(Set a, b)]
assocs (TotalMap mappings) = mappings
