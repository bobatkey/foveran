module Data.FreeMonad
    ( FM (..)
    )
    where

data FM f a = Layer (f (FM f a))
            | Var   a
