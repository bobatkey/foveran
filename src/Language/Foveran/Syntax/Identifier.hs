{-# LANGUAGE DeriveFunctor,
             GeneralizedNewtypeDeriving,
             OverloadedStrings #-}

module Language.Foveran.Syntax.Identifier
    ( Ident
    , NameSupply ()
    , getBound
    , bind
    , bindDummy
    , bindK
    , runNameSupply
    )
    where

import           Control.Applicative
import           Data.Monoid (mappend)
import qualified Data.Text as T
import qualified Data.Set  as S

type Ident = T.Text

newtype NameSupply a = NS { unNS :: (S.Set Ident, [Ident]) -> a }
    deriving (Functor, Applicative, Monad)

freshen used nm = if S.member nm used then freshen used (nm `mappend` "'") else (S.insert nm used, nm)

getBound :: Int -> NameSupply Ident
getBound i       = NS $ \(used, bound) -> bound !! i

bind :: Ident -> NameSupply a -> NameSupply (Ident, a)
bind nm (NS f)   = NS $ \(used, bound) -> let (used',nm') = freshen used nm in (nm', f (used', nm':bound))

bindDummy :: NameSupply a -> NameSupply a
bindDummy (NS f) = NS $ \(used, bound) -> f (used, undefined:bound) -- FIXME: wicked hack

bindK :: Ident -> NameSupply a -> (Ident -> a -> NameSupply b) -> NameSupply b
bindK nm x k = do (nm',x') <- bind nm x
                  k nm' x'

runNameSupply :: NameSupply a -> S.Set Ident -> a
runNameSupply (NS f) used = f (used, [])
