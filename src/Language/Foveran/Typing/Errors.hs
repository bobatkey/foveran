{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Errors
    ( TypeError (..)
    , ppTypeError
    , ppTerm
    , ppType
    )
    where

import           Text.PrettyPrint
import           Text.PrettyPrint.IsString
import           Language.Foveran.Typing.Context
import           Language.Foveran.Typing.Conversion (Value, reifyType0, reify)
import           Language.Foveran.Syntax.Checked (Ident, toDisplaySyntax)
import           Language.Foveran.Parsing.PrettyPrinter
import qualified Data.Text as T

data TypeError
    = ExpectingPiTypeForLambda    Context Value
    | ExpectingSigmaTypeForPair   Context Value
    | ExpectingSumTypeForInl      Context Value
    | ExpectingSumTypeForInr      Context Value
    | ExpectingUnitTypeForUnit    Context Value
    | ExpectingDescTypeForDesc    Context Value
    | ExpectingMuTypeForConstruct Context Value
    | UnknownIdentifier           Ident
    | ApplicationOfNonFunction    Context Value
    | CaseOnNonSum                Context Value
    | ExpectingSet
    | UnableToSynthesise
    | Proj1FromNonSigma           Context Value
    | Proj2FromNonSigma           Context Value
    | LevelProblem                Int Int
    | TypesNotEqual               Context Value Value
    | ReflCanOnlyProduceHomogenousEquality Context Value Value
    | ReflCanOnlyProduceEquality  Context Value Value Value
    | ReflExpectingEqualityType   Context Value
    | ElimEqCanOnlyHandleHomogenousEq Context Value Value
    | ExpectingEqualityType       Context Value

ppType :: Context -> Value -> Doc
ppType ctxt v =
  ppPlain $ contextNameSupply ctxt $ toDisplaySyntax $ reifyType0 v

ppTerm :: Context -> Value -> Value -> Doc
ppTerm ctxt v vty =
    ppPlain $ contextNameSupply ctxt $ toDisplaySyntax $ reify vty v 0


ppTypeError :: TypeError -> Doc
ppTypeError (ExpectingPiTypeForLambda ctxt ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term is a lambda-abstraction"
ppTypeError (ExpectingSigmaTypeForPair ctxt ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term constructs a pair"
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
ppTypeError (ExpectingMuTypeForConstruct ctxt ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term is an inductive type constructor"
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
ppTypeError (ReflCanOnlyProduceHomogenousEquality ctxt tyA tyB)
    = "'refl' can only produce homogenous equalities; types given:"
      $$ nest 4 (ppType ctxt tyA)
      $$ "and"
      $$ nest 4 (ppType ctxt tyB)
ppTypeError (ReflCanOnlyProduceEquality ctxt ty a b)
    = "Type checking 'refl', but terms"
      $$ nest 4 (ppTerm ctxt a ty)
      $$ "and"
      $$ nest 4 (ppTerm ctxt b ty)
      $$ "are not equal."
ppTypeError (ReflExpectingEqualityType ctxt ty)
    = "Term produces a value of equality type, checker is expecting the type"
      $$ nest 4 (ppType ctxt ty)
ppTypeError (ExpectingEqualityType ctxt ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term generates equalities"
