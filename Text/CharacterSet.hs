{-# LANGUAGE OverloadedStrings, TypeSynonymInstances #-}

-- |
-- Module      :  Text.CharacterSet
-- Copyright   :  Robert Atkey 2010
-- License     :  BSD3
--
-- Maintainer  :  bob.atkey@gmail.com
-- Stability   :  experimental
-- Portability :  unknown
--
-- Representation of unicode character sets, based on cset.ml from
-- Alain Frisch's ulex for ocaml. One difference is that because we
-- are using 'Char's to represent characters, the implementation has
-- to be more careful about going off the end of the range of
-- expressible characters.

module Text.CharacterSet
    (
      -- * Character set type
      CSet
    , anyChar
    , singleton 
    , interval
      
      -- * Useful Character Sets
    , xmlNameStartChar
    , xmlNameChar
    , mathematicalOperators
    , nameStartChar
    , nameChar
    , num
    , space)
    where

import Prelude hiding (null)
import Data.List (intercalate)
import Data.String
import Data.BooleanAlgebra
import Data.RangeSet

type CSet = Set Char

instance IsString CSet where
    fromString = foldl (.|.) zero . map singleton

anyChar :: CSet
anyChar = one

{-

{- Representation of character sets, copied from cset.ml from Alain
   Frisch's ulex for ocaml. Only difference is that because we are
   using 'Char's to represent characters, the implementation has to be
   more careful about going off the end of the range of expressible
   characters. -}

{- Character sets are represented as increasing, non-overlapping,
   non-empty lists of intervals -}

{- TODO: generalise this to any (Enum, Ord) type -}

-- TODO: coalescing of ranges that abutt. Seems to do this already?

-- | A set of unicode codepoints. Note that this type is an instance
-- of 'IsString', so character sets can be specified as literal
-- strings.
newtype CSet = CSet { unCSet :: [(Char,Char)] }
    deriving (Eq,Ord)

instance BooleanAlgebra CSet where
    (.&.)      = intersect
    (.|.)      = union
    complement = Text.CharacterSet.complement
    one        = anyChar
    zero       = empty

-- | Returns the list of ranges of unicode codepoints represented by
-- the given 'CSet'. The end points of each range are inclusive, and
-- the ranges are in increasing order.
ranges :: CSet -> [(Char,Char)]
ranges (CSet l) = l

instance Show CSet where
    show (CSet l) = "[" ++ intercalate "," (map showRange l) ++ "]"
        where showRange (l,h)
                  | l == h    = show l
                  | otherwise = show l ++ "-" ++ show h

-- | The empty set of unicode code points.
empty :: CSet
empty = CSet []

-- FIXME: could shortcut search if i > c.
-- | Test to determine whether the given 'Char' is in the 'CSet'.
memberOf :: Char -> CSet -> Bool
memberOf c (CSet l) = aux c l
    where
      aux c []        = False
      aux c ((i,j):l) = (i <= c && c <= j) || aux c l

-- | Returns an arbitrary character in the given set. Returns
-- 'Nothing' if the set is empty.
getRepresentative :: CSet -> Maybe Char
getRepresentative (CSet [])        = Nothing
getRepresentative (CSet ((i,_):_)) = Just i

-- | Set consisting of a single unicode code point.
singleton :: Char -> CSet
singleton c = CSet [(c,c)]

-- | Test to determine whether the given character set is empty.
null :: CSet -> Bool
null (CSet []) = True
null (CSet _)  = False

-- | Sets containing all the characters between the two given
-- endpoints, inclusive of these points. The arguments need not be in
-- any particular order.
interval :: Char -> Char -> CSet
interval i j = CSet $ if i <= j then [(i,j)] else [(j,i)]

-- | The set containing all unicode code points.
anyChar :: CSet
anyChar = interval minBound maxBound

instance IsString CSet where
    fromString = foldl union empty . map singleton

-- | Computes the union of two character sets, i.e. the set with all
-- the characters contained in the two arguments.
union :: CSet -> CSet -> CSet
union (CSet c1) (CSet c2) = CSet $ aux c1 c2
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
complement :: CSet -> CSet
complement = CSet . aux minBound . unCSet
    where
      aux start []      
          | start <= maxBound = [(start,maxBound)]
          | otherwise         = []
      aux start ((i,j):l)
          | start == i        = if j == maxBound then [] else aux (succ j) l
          | otherwise         = (start,pred i):if j == maxBound then [] else aux (succ j) l

-- | Computes the intersection of two sets. Returns the set containing
-- all the characters found in both of the given sets.
intersect :: CSet -> CSet -> CSet
intersect c1 c2 = Text.CharacterSet.complement (Text.CharacterSet.complement c1 `union` Text.CharacterSet.complement c2)

-}

{------------------------------------------------------------------------------}
-- Some character sets
-- FIXME: split this out?
xmlNameStartChar = singleton ':'
                   .|.
                   interval 'A' 'Z'
                   .|.
                   singleton '_'
                   .|.
                   interval 'a' 'z'
                   .|.
                   interval '\xc0' '\xd6'
                   .|.
                   interval '\xd8' '\xf6'
                   .|.
                   interval '\x370' '\x37d'
                   .|.
                   interval '\x37f' '\x1fff'
                   .|.
                   interval '\x200c' '\x200d'
                   .|.
                   interval '\x2070' '\x218f'
                   .|.
                   interval '\x2c00' '\x2fef'
                   .|.
                   interval '\x3001' '\xd7ff'
                   .|.
                   interval '\xf900' '\xFDCF'
                   .|.
                   interval '\xfdf0' '\xfffd'
                   .|.
                   interval '\x10000' '\xeffff'

xmlNameChar  = xmlNameStartChar
               .|.
               singleton '-'
               .|.
--               singleton '.'
--               .|.
               interval '0' '9'
               .|.
               singleton '\xb7'
               .|.
               interval '\x0300' '\x036f'
               .|.
               interval '\x203f' '\x2040'

mathematicalOperators = interval '\x2200' '\x22ff'

nameStartChar = xmlNameStartChar .|. mathematicalOperators
nameChar = xmlNameChar .|. mathematicalOperators .|. singleton '\''

num = interval '0' '9'

space :: CSet
space = " \n\t"
