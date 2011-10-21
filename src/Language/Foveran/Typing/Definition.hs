{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Definition
    ( processDefinition )
    where

import qualified Data.Text as T

import           Control.Monad (unless)
import           Text.PrettyPrint
import           Text.PrettyPrint.IsString ()
import           Control.Monad.IO.Class (liftIO)
import           Language.Foveran.Syntax.Display (Definition (..))
import           Language.Foveran.Syntax.LocallyNameless (toLocallyNamelessClosed)
import           Language.Foveran.Parsing.PrettyPrinter (ppAnnotTerm)
import           Language.Foveran.Typing.DeclCheckMonad

processDefinition :: Definition -> DeclCheckM ()
processDefinition (Definition p nm extTy nm' extTm) =
    do unless (nm == nm') $ malformedDefinition p nm nm'
       liftIO $ do putStrLn ("Checking definition: " ++ T.unpack nm)
                   putStrLn $ render $ (   "Type: " <+> ppAnnotTerm extTy
                                        $$ "Term: " <+> ppAnnotTerm extTm)
                   putStrLn ""
       let ty = toLocallyNamelessClosed extTy
           tm = toLocallyNamelessClosed extTm
       checkInternalDefinition p nm ty (Just tm)

