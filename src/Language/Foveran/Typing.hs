{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing
    ( checkDeclarations )
    where

import Text.Position (Span)

import Language.Foveran.Syntax.Display (Declaration (..), Datatype (..))
import Language.Foveran.Typing.DeclCheckMonad
import Language.Foveran.Typing.Assume ( processAssumeDecl )
import Language.Foveran.Typing.Normalise ( doNormalise )
import Language.Foveran.Typing.DataDecl ( genDesc, genDatatypeCarrier, genConstructors )
import Language.Foveran.Typing.IDataDecl ( processIDataDecl )
import Language.Foveran.Typing.Conversion.Value ( vliftTy, vlift
                                                , vliftITy, vliftI
                                                )

checkDeclarations :: [Declaration] -> IO ()
checkDeclarations decls =
    runDeclCheckM $ do
      extend undefined "lift" vliftTy (Just vlift)
      extend undefined "liftI" vliftITy (Just vliftI)
      mapM_ checkDecl decls

-- FIXME: move this (or make it obsolete)
checkDatatype :: Datatype -> DeclCheckM Span ()
checkDatatype d =
    do checkDefinition (genDesc d)
       checkDefinition (genDatatypeCarrier d)
       mapM_ checkDefinition (genConstructors d)


checkDecl :: Declaration -> DeclCheckM Span ()
checkDecl (AssumptionDecl a) = processAssumeDecl a
checkDecl (DefinitionDecl d) = checkDefinition d
checkDecl (DatatypeDecl d)   = checkDatatype d
checkDecl (Normalise tm)     = doNormalise tm
checkDecl (IDataDecl d)      = processIDataDecl d
