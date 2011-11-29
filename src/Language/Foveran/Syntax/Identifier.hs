{-# LANGUAGE DeriveFunctor,
             GeneralizedNewtypeDeriving,
             OverloadedStrings #-}

module Language.Foveran.Syntax.Identifier
    ( Ident
    , (<+>)
    , UsesIdentifiers (..)
    , freshFor
    , NameGeneration ()
    , getBound
    , bind
    , bindDummy
    , bindK
    , runNameGeneration
    , runNameGenerationWith
    )
    where

import           Control.Applicative
import           Data.Monoid (mappend)
import qualified Data.Text as T
import qualified Data.Set  as S

type Ident = T.Text

class UsesIdentifiers a where
    usedIdentifiers :: a -> S.Set Ident

newtype NameGeneration a = NG { unNG :: (S.Set Ident, [Ident]) -> a }
    deriving (Functor, Applicative, Monad)

freshFor :: UsesIdentifiers s => s -> Ident -> Ident
freshFor s nm = snd (freshen (usedIdentifiers s) nm)

-- FIXME: find a better way of freshening names
freshen :: S.Set Ident -> Ident -> (S.Set Ident, Ident)
freshen used nm = loop variants
    where loop (nm:nms) = if S.member nm used then loop nms else (S.insert nm used, nm)

          variants = nm:[ nm `mappend` (T.pack $ show i) | i <- [0..]]

getBound :: Int -> NameGeneration Ident
getBound i = NG $ \(used, bound) -> if i > length bound then error ("index too large: " ++ show i) else bound !! i

bind :: Ident -> NameGeneration a -> NameGeneration (Ident, a)
bind nm (NG f)   = NG $ \(used, bound) -> let (used',nm') = freshen used nm in (nm', f (used', nm':bound))

bindDummy :: NameGeneration a -> NameGeneration a
bindDummy (NG f) = NG $ \(used, bound) -> f (used, undefined:bound) -- FIXME: wicked hack: change this to use Maybes

bindK :: Ident -> NameGeneration a -> (Ident -> a -> NameGeneration b) -> NameGeneration b
bindK nm x k = do (nm',x') <- bind nm x
                  k nm' x'

{-
bind2 :: Ident -> Ident -> NameGeneration a ->
         (Ident -> Ident -> a -> NameGeneration b) ->
         NameGeneration b
bind2 nm1 nm2 x k = do (nm1',x') <- bind nm1 x
                       (nm2',x'') <- bind nm2 x'
                       k nm1 nm2 x''
-}

runNameGeneration :: UsesIdentifiers s => s -> NameGeneration a -> a
runNameGeneration s (NG f) = f (usedIdentifiers s, [])

runNameGenerationWith :: UsesIdentifiers s => s -> [Ident] -> NameGeneration a -> a
runNameGenerationWith s idents (NG f) = f (usedIdentifiers s, idents)

(<+>) :: Ident -> T.Text -> Ident
nm <+> t = T.append nm t