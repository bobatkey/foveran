{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing
    ( checkDeclarations )
    where

import Language.Foveran.Typing.DeclCheckMonad
import Language.Foveran.Syntax.Display (Declaration (..))
import Language.Foveran.Typing.Assume ( processAssumeDecl )
import Language.Foveran.Typing.Normalise ( doNormalise )
import Language.Foveran.Typing.DataDecl ( checkDatatype )
import Language.Foveran.Typing.IDataDecl ( processIDataDecl )
import Language.Foveran.Typing.Definition (processDefinition)
import Language.Foveran.Typing.Conversion.Value ( vliftTy, vlift
                                                , vliftITy, vliftI
                                                )

checkDeclarations :: [Declaration] -> IO ()
checkDeclarations decls =
    runDeclCheck $ do
      extend undefined "lift" vliftTy (Just vlift)
      extend undefined "liftI" vliftITy (Just vliftI)
      mapM_ checkDecl decls

checkDecl :: Declaration -> DeclCheckM ()
checkDecl (AssumptionDecl a) = processAssumeDecl a
checkDecl (DefinitionDecl d) = processDefinition d
checkDecl (DatatypeDecl d)   = checkDatatype d
checkDecl (Normalise tm)     = doNormalise tm
checkDecl (IDataDecl d)      = processIDataDecl d
