{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing
    ( checkDeclarations )
    where

import Language.Foveran.Syntax.Display (Declaration)
import Language.Foveran.Typing.DeclCheckMonad
import Language.Foveran.Typing.Conversion.Value (vsemTy, vsem, vliftTy, vlift)

checkDeclarations :: [Declaration] -> IO ()
checkDeclarations decls =
    runDeclCheckM $ do
      extend undefined "sem" vsemTy (Just vsem)
      extend undefined "lift" vliftTy (Just vlift)
      mapM_ checkDecl decls
