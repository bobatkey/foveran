{-# LANGUAGE OverloadedStrings #-}
-- | The interface to the normaliser

module Language.Foveran.Typing.Normalise
    where

import Text.PrettyPrint
import Text.PrettyPrint.IsString ()
import Text.Position
import qualified Language.Foveran.Syntax.Display as DS
import qualified Language.Foveran.Syntax.Checked as CS
import Language.Foveran.Parsing.PrettyPrinter
import Language.Foveran.Syntax.LocallyNameless (toLocallyNamelessClosed)
import Language.Foveran.Typing.DeclCheckMonad
import Language.Foveran.Typing.Checker
import Language.Foveran.Typing.Errors
import Language.Foveran.Typing.Context

doNormalise :: DS.TermPos -> DeclCheckM ()
doNormalise tmDS = do
  let tm = toLocallyNamelessClosed tmDS
  (ty,c) <- liftTyCheck $ tySynth tm
  v <- evaluate c
  ctxt <- getContext
  let d  = ppTerm ctxt v ty
      d0 = ppPlain $ contextNameSupply ctxt $ CS.toDisplaySyntax c
  liftIO $ putStrLn $ render ("normalised: "
                              $$ nest 4 d0
                              $$ "of type"
                              $$ nest 4 (ppType ctxt ty)
                              $$ "to"
                              $$ nest 4 d
                              $$ "")
  return ()
