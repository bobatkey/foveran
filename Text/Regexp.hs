{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

module Text.Regexp
    ( Regexp ()
    , (.>>.)
    , star
    , zeroOrMore
    , oneOrMore
    , tok)
    where

import qualified Data.Set as S
import           Data.String
import           Data.RangeSet
import           Text.CharacterSet
import qualified Text.Regexp.DFA as DFA
import           Data.BooleanAlgebra
import           Control.Arrow (first)
import           Data.List  (find)
import           Data.Maybe (isJust)

{------------------------------------------------------------------------------}
-- move this to Text.CharacterSet when the stuff with exhaustive
-- partitions is done
andClasses :: S.Set CSet -> S.Set CSet -> S.Set CSet
andClasses x y = S.fromList [ a .&. b | a <- S.elems x, b <- S.elems y ]

classesN :: Regexp -> S.Set CSet
classesN (NSeq ns) = classesNs ns
    where
      classesNs []        = S.singleton one
      classesNs (n:ns) 
          | matchesEmptyN n = classesN n `andClasses` classesNs ns
          | otherwise       = classesN n
classesN (NAlt ns) = foldr andClasses (S.fromList [zero, one]) $ map classesN $ S.elems ns
classesN (NTok c)  = S.fromList [c, complement c]
classesN (NStar n) = classesN n
classesN (NAnd ns) = foldr andClasses (S.fromList [zero, one]) $ map classesN $ S.elems ns
classesN (NNot n)  = classesN n

{------------------------------------------------------------------------------}
-- Class instance

boolToMaybe True  = Just ()
boolToMaybe False = Nothing

instance DFA.RegexpLike Regexp where
    type DFA.Result Regexp = ()
    diff c         = diffN c {- norm . diffRE c . forget -}
    matchesNothing = matchesNothingN {- matchesNothingRE . forget -}
    matchesEmpty   = boolToMaybe . matchesEmptyN {- boolToMaybe . matchesEmptyRE . forget -}
    classes        = classesN -- classesRE . forget

-- FIXME: this is only here because the 'andClasses' function is
-- here. It should really be in Text.Regexp.DFA. And the 'andClasses'
-- function should be in 
instance (DFA.RegexpLike r, DFA.Result r ~ (), Ord a) => DFA.RegexpLike [(r,a)] where
    type DFA.Result [(r,a)] = a
    diff c         = map (first $ DFA.diff c)
    matchesNothing = all (DFA.matchesNothing . fst)
    matchesEmpty   = fmap snd . find (isJust . DFA.matchesEmpty . fst)
    classes        = foldl andClasses (S.fromList [zero,one]) . map (DFA.classes . fst)

{------------------------------------------------------------------------------}
matchesNothingN :: Regexp -> Bool
matchesNothingN (NSeq ns) = or $ map matchesNothingN ns
matchesNothingN (NAlt ns) = and $ map matchesNothingN $ S.elems ns
matchesNothingN (NTok c)  = Data.RangeSet.null c
matchesNothingN (NAnd ns) = and $ map matchesNothingN $ S.elems ns
matchesNothingN (NNot n)  = not $ matchesNothingN n
matchesNothingN (NStar _) = False

matchesEmptyN :: Regexp -> Bool
matchesEmptyN (NSeq ns) = and $ map matchesEmptyN ns
matchesEmptyN (NAlt ns) = or $ map matchesEmptyN $ S.elems ns
matchesEmptyN (NTok c)  = False
matchesEmptyN (NStar _) = True
matchesEmptyN (NNot n)  = not $ matchesEmptyN n
matchesEmptyN (NAnd ns) = and $ map matchesEmptyN $ S.elems ns

diffN :: Char -> Regexp -> Regexp
diffN c (NSeq ns)  = diffNs ns
    where
      diffNs []     = nZero
      diffNs (n:ns) 
          | matchesEmptyN n = (diffN c n `nSeq` NSeq ns) `nAlt` diffNs ns
          | otherwise       = diffN c n `nSeq` NSeq ns
diffN c (NAlt ns)  = foldr nAlt nZero $ map (diffN c) $ S.elems ns
diffN c (NTok cl)
    | c `memberOf` cl = nEps
    | otherwise       = nZero
diffN c (NStar ns) = diffN c ns `nSeq` NStar ns
diffN c (NAnd ns)  = foldr nAnd nTop $ map (diffN c) $ S.elems ns
diffN c (NNot n)   = NNot (diffN c n)

{------------------------------------------------------------------------------}
data Regexp
    = NSeq  [Regexp]
    | NAlt  (S.Set Regexp)
    | NTok  CSet
    | NAnd  (S.Set Regexp)
    | NNot  Regexp
    | NStar Regexp
      deriving (Eq, Ord, Show)

instance IsString Regexp where
    fromString s = NSeq $ map (NTok . singleton) s

instance BooleanAlgebra Regexp where
    (.&.)      = nAnd
    (.|.)      = nAlt
    complement = NNot
    one        = nTop
    zero       = nZero

(.>>.) :: Regexp -> Regexp -> Regexp
(.>>.) = nSeq

star :: Regexp -> Regexp
star n = NStar n

zeroOrMore :: Regexp -> Regexp
zeroOrMore = star

oneOrMore :: Regexp -> Regexp
oneOrMore n = n .>>. star n

tok :: CSet -> Regexp
tok cs = NTok cs

nEps  = NSeq []
nZero = NAlt S.empty
nTop  = NNot nZero

isBottom (NAlt s) = S.null s
isBottom _        = False

isTop (NNot x) = isBottom x
isTop _        = False

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

nStar (NStar r) = NStar r
nStar (NSeq []) = NSeq []
nStar x | isBottom x = NSeq []
        | otherwise  = NStar x
