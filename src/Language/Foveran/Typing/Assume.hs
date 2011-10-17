module Language.Foveran.Typing.Assume
    ( processAssumeDecl )
    where

import Text.Position (Span)

import Language.Foveran.Syntax.Display
import Language.Foveran.Syntax.LocallyNameless (toLocallyNamelessClosed)
import Language.Foveran.Typing.DeclCheckMonad

processAssumeDecl :: AssumeDecl -> DeclCheckM ()
processAssumeDecl (Assume p nm ty) = do
  let t = toLocallyNamelessClosed ty
  checkInternalDefinition p nm t Nothing
