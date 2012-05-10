{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Errors
    ( TypeError (..)
    , ppTypeError
    , ppTerm
    , ppType
    , DataDeclError (..)
    , ppDataDeclError
    )
    where

import           Text.PrettyPrint
import           Language.Foveran.Syntax.Identifier (Ident, UsesIdentifiers, runNameGeneration)
import qualified Language.Foveran.Syntax.LocallyNameless as LN
import           Language.Foveran.Syntax.Checked (toDisplaySyntax)
import           Language.Foveran.Typing.Context
import           Language.Foveran.Typing.Conversion (Value, reifyType0, reify)
import           Language.Foveran.Parsing.PrettyPrinter

{------------------------------------------------------------------------------}
data TypeError
    = ExpectingPiTypeForLambda    Value
    | ExpectingSigmaTypeForPair   Value
    | ExpectingSumTypeForInl      Value
    | ExpectingSumTypeForInr      Value
    | ExpectingUnitTypeForUnit    Value
    | ExpectingDescTypeForDesc    Value
    | ExpectingMuTypeForConstruct Value
    | UnknownIdentifier           Ident
    | ApplicationOfNonFunction    Value
    | CaseOnNonSum                Value
    | ExpectingSet
    | UnableToSynthesise          LN.TermPos
    | Proj1FromNonSigma           Value
    | Proj2FromNonSigma           Value
    | LevelProblem                Int Int
    | TypesNotEqual               Value Value
    | ReflCanOnlyProduceHomogenousEquality Value Value
    | ReflCanOnlyProduceEquality  Value Value Value
    | ReflExpectingEqualityType   Value
    | ElimEqCanOnlyHandleHomogenousEq Value Value
    | ExpectingEqualityType       Value
    | ExpectingIDescForSemI       Value

ppType :: UsesIdentifiers ctxt =>
          ctxt
       -> Value
       -> Doc
ppType ctxt v =
    ppPlain $ runNameGeneration ctxt $ toDisplaySyntax $ reifyType0 v

ppTerm :: UsesIdentifiers ctxt =>
          ctxt
       -> Value
       -> Value
       -> Doc
ppTerm ctxt v vty =
    ppPlain $ runNameGeneration ctxt $ toDisplaySyntax $ reify vty v 0


ppTypeError :: UsesIdentifiers ctxt => ctxt -> TypeError -> Doc
ppTypeError ctxt (ExpectingPiTypeForLambda ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term is a lambda-abstraction"
ppTypeError ctxt (ExpectingSigmaTypeForPair ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term constructs a pair"
ppTypeError ctxt (ExpectingSumTypeForInl ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term is a left injection"
ppTypeError ctxt (ExpectingSumTypeForInr ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term is a right injection"
ppTypeError ctxt (ExpectingUnitTypeForUnit ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term has type 𝟙"
ppTypeError ctxt (ExpectingDescTypeForDesc ty)
    = "Expecting Desc type for description"
ppTypeError ctxt (ExpectingMuTypeForConstruct ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term is an inductive type constructor"
ppTypeError ctxt (UnknownIdentifier nm)
    = "Unknown identifier" <+> "“" <> ppIdent nm <> "”"
ppTypeError ctxt (ApplicationOfNonFunction ty)
    = "Application of non function"
ppTypeError ctxt (CaseOnNonSum ty)
    = "Case on value of non-sum type"
ppTypeError ctxt (ExpectingSet)
    = "Expecting a term of sort Set"
ppTypeError ctxt (UnableToSynthesise t)
    = "Unable to synthesise type for this term: " <> text (show t)
ppTypeError ctxt (Proj1FromNonSigma ty)
    = "First projection from non Sigma-type"
ppTypeError ctxt (Proj2FromNonSigma ty)
    = "Second projection from non Sigma-type"
ppTypeError ctxt (LevelProblem i j)
    = "Level problem:" <+> int i <+> "not <=" <+> int j
ppTypeError ctxt (TypesNotEqual ty1 ty2)
    = "Expecting term to have type "
      $$ nest 4 (ppType ctxt ty1)
      $$ "but term has type"
      $$ nest 4 (ppType ctxt ty2)
ppTypeError ctxt (ReflCanOnlyProduceHomogenousEquality tyA tyB)
    = "'refl' can only produce homogenous equalities; types given:"
      $$ nest 4 (ppType ctxt tyA)
      $$ "and"
      $$ nest 4 (ppType ctxt tyB)
ppTypeError ctxt (ReflCanOnlyProduceEquality ty a b)
    = "Type checking 'refl', but terms"
      $$ nest 4 (ppTerm ctxt a ty)
      $$ "and"
      $$ nest 4 (ppTerm ctxt b ty)
      $$ "are not equal."
ppTypeError ctxt (ReflExpectingEqualityType ty)
    = "Term produces a value of equality type, checker is expecting the type"
      $$ nest 4 (ppType ctxt ty)
ppTypeError ctxt (ElimEqCanOnlyHandleHomogenousEq ty1 ty2)
    = "Equality elimination can only handle elimination of homogenous equalities, types involved are:"
      $$ nest 4 (ppType ctxt ty1)
      $$ "and"
      $$ nest 4 (ppType ctxt ty2)
ppTypeError ctxt (ExpectingEqualityType ty)
    = "Expecting term to have type"
      $$ nest 4 (ppType ctxt ty)
      $$ "but this term generates equalities"
ppTypeError ctxt (ExpectingIDescForSemI ty)
    = "Expecting term to have indexed description type, but type is"
      $$ nest 4 (ppType ctxt ty)

{------------------------------------------------------------------------------}
data DataDeclError
    = DuplicateParameterName      Ident
    | DuplicateConstructorName    Ident
    | ShadowingDatatypeName
    | ShadowingParameterName
    | ConstructorTypesMustEndWithNameOfDatatype Ident Ident
    | NonMatchingParameterArgument Ident Ident
    | IllFormedArgument            Ident
    | TooManyArgumentsForDatatype
    | NotEnoughArgumentsForDatatype

ppDataDeclError :: DataDeclError -> Doc
ppDataDeclError (DuplicateConstructorName ident)
    = "Duplicate constructor name: '" <> ppIdent ident <> "'"
ppDataDeclError (DuplicateParameterName ident)
    = "Duplicate parameter name: '" <> ppIdent ident <> "'"
ppDataDeclError (ShadowingDatatypeName)
    = "Shadowing of the data type's name in constructor definition"
ppDataDeclError (ShadowingParameterName)
    = "Shadowing of a parameter name in constructor definition"
ppDataDeclError (ConstructorTypesMustEndWithNameOfDatatype givenNm expectedNm)
    = "Constructor types must end with the name of the datatype being defined: '" <> ppIdent expectedNm <> "', not '" <> ppIdent givenNm <> "'"
ppDataDeclError (NonMatchingParameterArgument givenNm expectedNm)
    = "Parameter argument has incorrect name: should be '" <> ppIdent expectedNm <> "', not '" <> ppIdent givenNm <> "'"
ppDataDeclError (IllFormedArgument expectedNm)
    = "Ill-formed parameter argument: should be '" <> ppIdent expectedNm <> "'"
ppDataDeclError (TooManyArgumentsForDatatype)
    = "Too many arguments for data type in constructor declaration"
ppDataDeclError (NotEnoughArgumentsForDatatype)
    = "Not enough arguments for data type in constructor declaration"
