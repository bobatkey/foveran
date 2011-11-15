{-# LANGUAGE OverloadedStrings #-}
-- | The interface to the normaliser

module Language.Foveran.Typing.Normalise
    ( processNormalise )
    where

import Control.Monad.IO.Class (liftIO)
import Text.PrettyPrint
import Text.PrettyPrint.IsString ()
import Data.Rec (AnnotRec (Annot))
import qualified Language.Foveran.Syntax.Display as DS
import qualified Language.Foveran.Syntax.Checked as CS
import Language.Foveran.Parsing.PrettyPrinter
import Language.Foveran.Syntax.Identifier (runNameGeneration)
import Language.Foveran.Syntax.LocallyNameless (toLocallyNamelessClosed)
import Language.Foveran.Typing.DeclCheckMonad
import Language.Foveran.Typing.Checker (synthesiseTypeFor)
import Language.Foveran.Typing.Errors
import Language.Foveran.Typing.Context

processNormalise :: DS.TermPos -> DeclCheckM ()
processNormalise tmDS = do
  let tm@(Annot p _) = toLocallyNamelessClosed tmDS
  (ty,c) <- runTypingNoHoles p $ synthesiseTypeFor tm
  v <- evaluate c
  ctxt <- getContext
  let d  = ppTerm ctxt v ty
      d0 = ppPlain $ runNameGeneration ctxt $ CS.toDisplaySyntax c
  liftIO $ putStrLn $ render ("normalised: "
                              $$ nest 4 d0
                              $$ "of type"
                              $$ nest 4 (ppType ctxt ty)
                              $$ "to"
                              $$ nest 4 d
                              $$ "")
