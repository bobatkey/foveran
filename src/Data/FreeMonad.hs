module Data.FreeMonad where

data FM f a = Layer (f (FM f a))
            | Var   a
