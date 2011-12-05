{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing
    ( checkDeclarations )
    where

import Language.Foveran.Typing.DeclCheckMonad
import Language.Foveran.Syntax.Display (Declaration (..))
import Language.Foveran.Typing.Assume (processAssumeDecl)
import Language.Foveran.Typing.Normalise (processNormalise)
import Language.Foveran.Typing.DataDecl (checkDatatype)
import Language.Foveran.Typing.IDataDecl (processIDataDecl)
import Language.Foveran.Typing.Definition (processDefinition)
import Language.Foveran.Typing.Conversion.Value ( vliftTy, vlift
                                                )

checkDeclarations :: [Declaration] -> IO ()
checkDeclarations decls =
    runDeclCheck $ do
      extend undefined "lift" vliftTy (Just vlift)
      mapM_ checkDecl decls

checkDecl :: Declaration -> DeclCheckM ()
checkDecl (AssumptionDecl a) = processAssumeDecl a
checkDecl (DefinitionDecl d) = processDefinition d
checkDecl (DatatypeDecl d)   = checkDatatype d
checkDecl (Normalise tm)     = processNormalise tm
checkDecl (IDataDecl d)      = processIDataDecl d
