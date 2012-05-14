module Language.Foveran.Syntax.Common
    ( Abelian (..)
    )
    where

data Abelian
    = IsAbelian
    | NotAbelian
    deriving (Show, Eq, Ord)
