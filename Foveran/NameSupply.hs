{-# LANGUAGE DeriveFunctor,
             GeneralizedNewtypeDeriving,
             OverloadedStrings #-}

module Foveran.NameSupply where

import           Control.Applicative
import           Data.Monoid (mappend)
import qualified Data.Text as T
import qualified Data.Set  as S

type Ident = T.Text

class Applicative f => NameSupply f where
  getBound  :: Int -> f Ident
  bind      :: Ident -> f a -> f a
  bindDummy :: f a -> f a

newtype NS a = NS { unNS :: (S.Set Ident, [Ident]) -> a }
            deriving (Functor, Applicative)

freshen used nm = if S.member nm used then freshen used (nm `mappend` "'") else (S.insert nm used, nm)

instance NameSupply NS where
  getBound i       = NS $ \(used, bound) -> bound !! i
  bind nm (NS f)   = NS $ \(used, bound) -> let (used',nm') = freshen used nm in f (used',nm':bound)
  bindDummy (NS f) = NS $ \(used, bound) -> f (used, undefined:bound) -- FIXME: wicked hack