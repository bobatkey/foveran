{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing
    ( checkDeclarations )
    where

import Language.Foveran.Syntax.Display (Declaration)
import Language.Foveran.Typing.DeclCheckMonad
import Language.Foveran.Typing.Conversion.Value ( vliftTy, vlift
                                                , vliftITy, vliftI
                                                )

checkDeclarations :: [Declaration] -> IO ()
checkDeclarations decls =
    runDeclCheckM $ do
      extend undefined "lift" vliftTy (Just vlift)
      extend undefined "liftI" vliftITy (Just vliftI)
      mapM_ checkDecl decls
