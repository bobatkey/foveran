module Data.Pair where

import Control.Applicative
import Data.Monoid
import Data.Foldable
import Data.Traversable

data Pair a = Pair a a
              deriving (Show, Eq, Ord)

instance Functor Pair where
    fmap f (Pair x y) = Pair (f x) (f y)

instance Foldable Pair where
    fold      (Pair x y) = x `mappend` y
    foldMap f (Pair x y) = f x `mappend` f y

instance Traversable Pair where
    traverse f (Pair x y) = Pair <$> f x <*> f y
    sequenceA  (Pair x y) = Pair <$> x <*> y