module Data.FreeMonad
    ( FM (..)
    )
    where

import Control.Applicative
import Control.Monad

data FM f a = Layer (f (FM f a))
            | Var   a

instance Functor f => Monad (FM f) where
    return = Var
    Var a   >>= k = k a
    Layer x >>= k = Layer (fmap (>>= k) x)

instance Functor f => Functor (FM f) where
    fmap = liftA

instance Functor f => Applicative (FM f) where
    pure = return
    (<*>) = ap