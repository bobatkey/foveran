module Language.Foveran.Typing.Definition
    ( processDefinition )
    where

import           Control.Monad (unless)
import           Language.Foveran.Syntax.Display (Definition (..))
import           Language.Foveran.Syntax.LocallyNameless (toLocallyNamelessClosed)
import           Language.Foveran.Typing.DeclCheckMonad

processDefinition :: Definition -> DeclCheckM ()
processDefinition (Definition p nm extTy nm' extTm) =
    do unless (nm == nm') $ malformedDefinition p nm nm'
       let ty = toLocallyNamelessClosed extTy
           tm = toLocallyNamelessClosed extTm
       checkInternalDefinition p nm ty (Just tm)
