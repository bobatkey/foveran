module Language.Foveran.Typing.LocalContext
    ( LocalContext ()
    , emptyLocalContext
    , localContextMembers
    , extendWith
    )
    where

import           Language.Foveran.Syntax.Identifier (Ident, UsesIdentifiers (..))
import           Language.Foveran.Typing.Conversion.Value (Value)
import           Language.Foveran.Typing.DefinitionContext
import qualified Data.Set as S

data LocalContext
    = LocalContext { localContextMembers    :: [(Ident, Value)]
                   , localContextUsedIdents :: S.Set Ident
                   }

instance DefinitionContext LocalContext where
    lookupDefinition identifier localContext =
        case lookup identifier (localContextMembers localContext) of
          Nothing  -> Nothing
          Just typ -> Just (typ, Nothing)

instance UsesIdentifiers LocalContext where
    usedIdentifiers = localContextUsedIdents

emptyLocalContext :: LocalContext
emptyLocalContext = LocalContext [] S.empty

-- FIXME: add a check to ensure that the identifier is fresh
extendWith :: Ident -> Value -> LocalContext -> LocalContext
extendWith identifier typ localContext
    = LocalContext { localContextMembers    = (identifier, typ) : localContextMembers localContext
                   , localContextUsedIdents = S.insert identifier (localContextUsedIdents localContext)
                   }
