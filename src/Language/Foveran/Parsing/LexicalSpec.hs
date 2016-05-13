{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}

module Language.Foveran.Parsing.LexicalSpec
    ( lexicalSpec )
    where

import Language.Foveran.Lexing.Spec
import Language.Foveran.Parsing.Layout
import Language.Foveran.Parsing.Token

emit = Emit . Token

lexicalSpec :: CompiledLexSpec (Action (NewlineOr Token))
lexicalSpec = $([|compileLexicalSpecification
    [ "assume" :==>          emit Assume
    , "normalise" :==>       emit Normalise
    , ":" :==>               emit Colon
    , ";" :==>               emit Semicolon
    , "=" :==>               emit Equals
    , "\\" .|. "\x03bb" :==> emit Lambda
    , "->" .|. "→" :==>      emit Arrow
    , "(" :==>               emit LParen
    , ")" :==>               emit RParen
    , "×" :==>               emit Times
    , "“×”" :==>             emit QuoteTimes
    , "+" :==>               emit Plus
    , "fst" :==>             emit Fst
    , "snd" :==>             emit Snd
    , "inl" :==>             emit Inl
    , "inr" :==>             emit Inr
    , "“K”" .|. "\"K\"" :==> emit QuoteK
    , "construct" :==>       emit Construct
    , "()" .|. "⋄" :==>      emit UnitValue
    , "«" :==>               emit LDoubleAngle
    , "»" :==>               emit RDoubleAngle
    , "," :==>               emit Comma
    , "case" :==>            emit Case
    , "for" :==>             emit For
    , "." :==>               emit FullStop
    , "with" :==>            emit With
    , "{" :==>               emit LBrace
    , "}" :==>               emit RBrace
    , "Set" :==>             emit Set
    , "Empty" .|. "𝟘" :==>   emit EmptyType
    , "Unit" .|. "𝟙" :==>    emit UnitType
    , "elimEmpty" :==>       emit ElimEmpty
    , "data" :==>            emit Data
    , "IDesc" :==>           emit IDesc
    , "“IId”".|. "\"IId\"" :==> emit Quote_IId
    , "“Σ”" .|. "\"Sg\"" :==> emit Quote_Sg
    , "“Π”" .|. "\"Pi\"" :==> emit Quote_Pi
    , "elimID" :==>          emit IDesc_Elim
    , "µI" .|. "muI" :==>    emit MuI
    , "≡" .|. "==" :==>     emit Eq
    , "refl" :==>            emit Refl
    , "rewriteBy" :==>       emit RewriteBy
    , "elimEq" :==>          emit ElimEq
    , "where" :==>           emit Where
    , "in" :==>              emit In
    , "_" :==>               emit Underscore
    , "then" :==>            emit Then
    , "absurdBy" :==>        emit AbsurdBy
    , "generalise" :==>      emit Generalise
    , "casesOn" :==>         emit CasesOn
    , "recursionOn" .|. "inductionOn"          :==> emit RecursionOn
    , "recurseOn" .|. "inductionHypothesisFor" :==> emit RecurseOn
    , "semI" :==>            emit SemI
    , "liftI" :==>           emit LiftI
    , "mapI" :==>            emit MapI
    , "bind" :==>            emit Bind
    , "<-" :==>              emit LeftArrow
    , "[" :==>               emit LSqBracket
    , "]" :==>               emit RSqBracket
    , "Group" :==>           emit Group
    , "AbGroup" :==>         emit AbGroup
    , "unit" :==>            emit GroupUnit
    , "#" :==>               emit GroupMul
    , "inv" :==>             emit GroupInv
    , "?" :==>               emit Hole
    , "eliminate" :==>       emit Eliminate
    , "return" :==>          emit Return
    , "call" :==>            emit Call
    , "<" :==>               emit LAngle
    , ">" :==>               emit RAngle
    , "`" .>>. tok (nameStartChar .&. complement (singleton '\x03bb')) .>>. zeroOrMore (tok nameChar) :==>
                             emit ConstructorName
    , tok (nameStartChar .&. complement (singleton '\x03bb')) .>>. zeroOrMore (tok nameChar) :==>
                             emit Ident
    , oneOrMore (tok digit) :==>
                             emit Number
    , "\n" :==>              Emit Newline
    , oneOrMore (tok (singleton ' ' .|. singleton '\t')) :==>
                             Ignore Whitespace
    , ("--" .|. "–") .>>. star (tok (complement (singleton '\n'))) :==>
                             Ignore Comment
    , "{-"
       .>>.
       (star (tok anyChar) .&. complement (star (tok anyChar) .>>. "-}" .>>. star (tok anyChar)))
       .>>.
       "-}" :==>             Ignore Comment
    ] |])
