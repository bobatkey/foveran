{-# LANGUAGE TypeOperators #-}

module Language.Foveran.Typing.DefinitionContext
    ( DefinitionContext (..)
    , lookupType
    , (:>:) (..)
    )
    where

import           Control.Applicative
import           Language.Foveran.Typing.Conversion.Value (Value)
import           Language.Foveran.Syntax.Identifier (Ident, UsesIdentifiers (..))
import qualified Data.Set as S

class DefinitionContext ctxt where
    lookupDefinition :: Ident -> ctxt -> Maybe (Value, Maybe Value)

lookupType :: DefinitionContext ctxt => Ident -> ctxt -> Maybe Value
lookupType identifier ctxt = fst <$> lookupDefinition identifier ctxt

{------------------------------------------------------------------------------}
data a :>: b = a :>: b

instance (DefinitionContext a, DefinitionContext b) => DefinitionContext (a :>: b) where
    lookupDefinition identifier (ctxt1 :>: ctxt2) =
        lookupDefinition identifier ctxt2 <|> lookupDefinition identifier ctxt1

instance (UsesIdentifiers a, UsesIdentifiers b) => UsesIdentifiers (a :>: b) where
    usedIdentifiers (a :>: b) = usedIdentifiers a `S.union` usedIdentifiers b
