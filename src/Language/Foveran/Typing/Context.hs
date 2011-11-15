{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Context
    ( Context ()
    , emptyContext
    , extendContext )
    where

import qualified Data.Map as M
import           Language.Foveran.Syntax.Identifier (Ident, UsesIdentifiers (..), freshFor)
import           Language.Foveran.Typing.Conversion (Value, DefinitionContext (..))

newtype Context
    = Context { getMapping :: M.Map Ident (Value, Maybe Value) }

emptyContext :: Context
emptyContext = Context M.empty

extendContext :: Context
              -> Ident
              -> Value
              -> Maybe Value
              -> Maybe Context
extendContext ctxt nm ty defn
    = case M.lookup nm (getMapping ctxt) of
        Nothing -> Just $ Context (M.insert nm (ty, defn) (getMapping ctxt))
        Just _  -> Nothing

instance DefinitionContext Context where
    lookupDefinition ident ctxt = M.lookup ident (getMapping ctxt)

instance UsesIdentifiers Context where
    usedIdentifiers ctxt = M.keysSet (getMapping ctxt)
