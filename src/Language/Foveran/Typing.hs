{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing
    ( checkDeclarations )
    where

import Language.Foveran.Syntax.Display (Declaration)
import Language.Foveran.Typing.DeclCheckMonad
import Language.Foveran.Typing.Conversion (vsemTy, vsem)

checkDeclarations :: [Declaration] -> IO ()
checkDeclarations decls =
    runDeclCheckM $ do
      extend undefined "sem" vsemTy (Just vsem)
      mapM_ checkDecl decls
