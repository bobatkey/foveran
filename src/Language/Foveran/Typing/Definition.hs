module Language.Foveran.Typing.Definition
    ( processDefinition )
    where

import           Control.Monad (unless)
import           Control.Monad.IO.Class (liftIO)
import           Data.Rec (AnnotRec (Annot))
import           Language.Foveran.Syntax.Display (Definition (..), TermCon(Lam))
import           Language.Foveran.Syntax.LocallyNameless (toLocallyNamelessClosed)
import           Language.Foveran.Typing.DeclCheckMonad

processDefinition :: Definition -> DeclCheckM ()
processDefinition (Definition p nm extTy nm' argPatterns extTm) =
    do liftIO $ putStrLn $ "Checking " ++ show nm
       unless (nm == nm') $ reportMalformedDefinition p nm nm'
       let ty = toLocallyNamelessClosed extTy
           tm = toLocallyNamelessClosed (case argPatterns of [] -> extTm; _ -> Annot p (Lam argPatterns extTm))
       checkDefinition p nm ty (Just tm)
