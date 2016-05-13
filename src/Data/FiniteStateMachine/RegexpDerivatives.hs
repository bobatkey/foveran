{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- |
-- Module          :  Data.FiniteStateMachine.RegexpDerivatives
-- Copyright       :  (C) Robert Atkey 2013
-- License         :  BSD3
--
-- Maintainer      :  bob.atkey@gmail.com
-- Stability       :  experimental
-- Portability     :  unknown
--
-- Regular expressions over an arbitrary bounded alphabet.

module Data.FiniteStateMachine.RegexpDerivatives
    ( Regexp ()
    , (.>>.)
    , star
    , zeroOrMore
    , oneOrMore
    , tok
    , module Data.BooleanAlgebra
    )
    where

import           Prelude hiding (all, any)
import qualified Data.Set as S
import           Data.BooleanAlgebra
import           Data.String (IsString (..))
import           Data.RangeSet
import           Data.FiniteStateMachine (FiniteStateMachine (..))
import           Control.Monad (guard)

-- | Regular expressions over an arbitrary alphabet.
data Regexp alphabet
    = NSeq  [Regexp alphabet]
    | NAlt  (S.Set (Regexp alphabet))
    | NTok  (Set alphabet)
    | NAnd  (S.Set (Regexp alphabet))
    | NNot  (Regexp alphabet)
    | NStar (Regexp alphabet)
    deriving (Eq, Ord, Show)

{------------------------------------------------------------------------------}
-- | Match a string literal exactly.
instance IsString (Regexp Char) where
    fromString s = NSeq $ map (NTok . singleton) s

-- | Regular expressions form alphabet boolean algebra.
instance Ord alphabet => BooleanAlgebra (Regexp alphabet) where
    (.&.)      = nAnd
    (.|.)      = nAlt
    complement = NNot
    one        = nTop
    zero       = nZero

-- | Sequencing of regular expressions.
instance Monoid (Regexp alphabet) where
    mempty  = NSeq []
    mappend = (.>>.)
    mconcat = NSeq

{------------------------------------------------------------------------------}
-- | Regular expressions are directly finite state machines via
-- Brzozowski derivatives.
instance (Ord alphabet, Enum alphabet, Bounded alphabet) =>
    FiniteStateMachine (Regexp alphabet) where
    data State    (Regexp alphabet)
        = RegexpState { unRegexpState :: Regexp alphabet }
          deriving (Eq, Ord)
    type Alphabet (Regexp alphabet) = alphabet
    type Result   (Regexp alphabet) = ()
    initState r        = RegexpState r
    advance _ c        = RegexpState . diffN c . unRegexpState
    isAcceptingState _ = guard . matchesEmptyN . unRegexpState
    classes _          = classesN . unRegexpState

{------------------------------------------------------------------------------}
matchesEmptyN :: Regexp alphabet -> Bool
matchesEmptyN (NSeq ns) = all matchesEmptyN ns
matchesEmptyN (NAlt ns) = any matchesEmptyN ns
matchesEmptyN (NTok c)  = False
matchesEmptyN (NStar _) = True
matchesEmptyN (NNot n)  = not (matchesEmptyN n)
matchesEmptyN (NAnd ns) = all matchesEmptyN ns

classesN :: (Enum alphabet, Bounded alphabet, Ord alphabet) =>
            Regexp alphabet
         -> Partition alphabet
classesN (NSeq ns) = classesNs ns
    where
      classesNs []          = fromSet one
      classesNs (n:ns)
          | matchesEmptyN n = classesN n `mappend` classesNs ns
          | otherwise       = classesN n
classesN (NAlt ns) = foldMap classesN ns
classesN (NTok c)  = fromSet c
classesN (NStar n) = classesN n
classesN (NAnd ns) = foldMap classesN ns
classesN (NNot n)  = classesN n

diffN :: Ord alphabet => alphabet -> Regexp alphabet -> Regexp alphabet
diffN c (NSeq ns)  = diffNs ns
    where
      diffNs []     = nZero
      diffNs (n:ns)
          | matchesEmptyN n = (diffN c n `nSeq` NSeq ns) `nAlt` diffNs ns
          | otherwise       = diffN c n `nSeq` NSeq ns
diffN c (NAlt ns)  = any (diffN c) ns
diffN c (NTok cl)
    | c `member` cl = nEps
    | otherwise     = nZero
diffN c (NStar ns) = diffN c ns `nSeq` NStar ns
diffN c (NAnd ns)  = all (diffN c) ns
diffN c (NNot n)   = NNot (diffN c n)


{------------------------------------------------------------------------------}
-- | Sequential sequencing of regular expressions.
(.>>.) :: Regexp alphabet -> Regexp alphabet -> Regexp alphabet
(.>>.) = nSeq

-- | @star re@ matches zero or more repetitions of @re@. Synonym of
-- 'zeroOrMore'.
star :: Regexp alphabet -> Regexp alphabet
star n = NStar n

-- | @zeroOrMore re@ matches zero or more repetitions of @re@. Synonym
-- of 'star'.
zeroOrMore :: Regexp alphabet -> Regexp alphabet
zeroOrMore = star

-- | @oneOrMore re@ matches one or more repetitions of
-- @re@. Equivalent to @re .>>. star re@.
oneOrMore :: Regexp alphabet -> Regexp alphabet
oneOrMore n = n .>>. star n

-- | A regular expression that accepts a single token from the given
-- set of tokens.
tok :: Set alphabet -> Regexp alphabet
tok cs = NTok cs

nEps :: Regexp alphabet
nEps  = NSeq []

nZero :: Regexp alphabet
nZero = NAlt S.empty

nTop :: Regexp alphabet
nTop  = NNot nZero

isBottom :: Regexp alphabet -> Bool
isBottom (NAlt s) = S.null s
isBottom _        = False

isTop :: Regexp alphabet -> Bool
isTop (NNot x) = isBottom x
isTop _        = False

nSeq :: Regexp alphabet
     -> Regexp alphabet
     -> Regexp alphabet
nSeq (NSeq x) (NSeq y) = NSeq (x ++ y)
nSeq x        (NSeq y)
    | isBottom x       = nZero
    | otherwise        = NSeq ([x] ++ y)
nSeq (NSeq x) y
    | isBottom y       = nZero
    | otherwise        = NSeq (x ++ [y])
nSeq x          y
    | isBottom x       = nZero
    | isBottom y       = nZero
    | otherwise        = NSeq [x,y]

nAlt :: Ord alphabet =>
        Regexp alphabet
     -> Regexp alphabet
     -> Regexp alphabet
nAlt (NAlt x) (NAlt y) = NAlt (S.union x y)
nAlt x        (NAlt y) 
    | isTop x          = NNot nZero
    | otherwise        = NAlt (S.insert x y)
nAlt (NAlt x) y        
    | isTop y          = NNot nZero
    | otherwise        = NAlt (S.insert y x)
nAlt x        y        
    | isTop x          = NNot nZero
    | isTop y          = NNot nZero
    | otherwise        = NAlt (S.fromList [x,y])

-- the cancellation rules are essential for termination of the DFA
-- construction algorithm (need the ones for 'and' as well as
-- 'or'. This is not mentioned in the Owens et al paper, but they
-- implement it anyway).
nAnd :: Ord alphabet =>
        Regexp alphabet
     -> Regexp alphabet
     -> Regexp alphabet
nAnd (NAnd x) (NAnd y) = NAnd (S.union x y)
nAnd x        (NAnd y) 
    | isTop x          = NAnd y
    | isBottom x       = nZero
    | otherwise        = NAnd (S.insert x y)
nAnd (NAnd x) y
    | isTop y          = NAnd x
    | isBottom y       = nZero
    | otherwise        = NAnd (S.insert y x)
nAnd x        y
    | isTop x          = y
    | isTop y          = x
    | isBottom x       = nZero
    | isBottom y       = nZero
    | otherwise        = NAnd (S.fromList [x,y])

-- I wonder why this isn't used?
-- nStar (NStar r) = NStar r
-- nStar (NSeq []) = NSeq []
-- nStar x | isBottom x = NSeq []
--         | otherwise  = NStar x
