{-# LANGUAGE OverloadedStrings #-}

module Foveran.Typing.Errors where

import           Text.PrettyPrint
import           Text.PrettyPrint.IsString
import           Foveran.Typing.Context
import           Foveran.Typing.Conversion (Value, reifyType0)
import           Foveran.Syntax.Checked (toDisplaySyntax)
import           Foveran.NameSupply (Ident)
import           Foveran.Parsing.PrettyPrinter
import qualified Data.Text as T

data TypeError
    = ExpectingPiTypeForLambda  Context Value
    | ExpectingSigmaTypeForPair Context Value
    | ExpectingSumTypeForInl    Context Value
    | ExpectingSumTypeForInr    Context Value
    | ExpectingUnitTypeForUnit  Context Value
    | ExpectingDescTypeForDesc  Context Value
    | UnknownIdentifier         Ident
    | ApplicationOfNonFunction  Context Value
    | CaseOnNonSum              Context Value
    | ExpectingSet
    | UnableToSynthesise
    | Proj1FromNonSigma         Context Value
    | Proj2FromNonSigma         Context Value
    | LevelProblem              Int Int
    | TypesNotEqual             Context Value Value

ppType :: Context -> Value -> Doc
ppType ctxt v =
  ppPlain $ contextNameSupply ctxt $ toDisplaySyntax $ reifyType0 v

ppTypeError :: TypeError -> Doc
ppTypeError (ExpectingPiTypeForLambda ctxt ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term is a lambda-abstraction"
ppTypeError (ExpectingSigmaTypeForPair ctxt ty)
    = "Expecting Sigma type for pair"
ppTypeError (ExpectingSumTypeForInl ctxt ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term is a left injection"
ppTypeError (ExpectingSumTypeForInr ctxt ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term is a right injection"
ppTypeError (ExpectingUnitTypeForUnit ctxt ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term has type 𝟙"
ppTypeError (ExpectingDescTypeForDesc ctxt ty)
    = "Expecting Desc type for description"
ppTypeError (UnknownIdentifier nm)
    = "Unknown identifier" <+> "“" <> text (T.unpack nm) <> "”"
ppTypeError (ApplicationOfNonFunction ctxt ty)
    = "Application of non function"
ppTypeError (CaseOnNonSum ctxt ty)
    = "Case on value of non-sum type"
ppTypeError (ExpectingSet)
    = "Expecting a term of sort Set"
ppTypeError (UnableToSynthesise)
    = "Unable to synthesise type for this term"
ppTypeError (Proj1FromNonSigma ctxt ty)
    = "First projection from non Sigma-type"
ppTypeError (Proj2FromNonSigma ctxt ty)
    = "Second projection from non Sigma-type"
ppTypeError (LevelProblem i j)
    = "Level problem:" <+> int i <+> "not <=" <+> int j
ppTypeError (TypesNotEqual ctxt ty1 ty2)
    = "Expecting term to have type "
      $$ nest 4 (ppType ctxt ty1)
      $$ "but term has type"
      $$ nest 4 (ppType ctxt ty2)
