{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}

module Language.Foveran.Parsing.LexicalSpec
    ( lexicalSpec )
    where

import Language.Forvie.Lexing.Spec
import Language.Forvie.Layout
import Language.Foveran.Parsing.Token

emit = Emit . Token

lexicalSpec :: CompiledLexSpec (Action (NewlineOr Token))
lexicalSpec = $([|compileLexicalSpecification
    [ "assume" :==>          emit Assume
    , "normalise" :==>       emit Normalise
    , ":" :==>               emit Colon
    , ":=" :==>              emit ColonEquals
    , ";" :==>               emit Semicolon
    , "=" :==>               emit Equals
    , "\\" .|. "\x03bb" :==> emit Lambda
    , "->" .|. "→" :==>      emit Arrow
    , "(" :==>               emit LParen
    , ")" :==>               emit RParen
    , "“→”" :==>             emit QuoteArrow
    , "×" :==>               emit Times
    , "“×”" :==>             emit QuoteTimes
    , "+" :==>               emit Plus
    , "“+”" :==>             emit QuotePlus
    , "fst" :==>             emit Fst
    , "snd" :==>             emit Snd
    , "inl" :==>             emit Inl
    , "inr" :==>             emit Inr
    , "“K”" .|. "\"K\"" :==> emit QuoteK
    , "µ" :==>               emit Mu
    , "construct" :==>       emit Construct
    , "induction" :==>       emit Induction
    , "elimD" :==>           emit ElimD
    , "sem" :==>             emit Sem
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
    , "“Id”" :==>            emit QuoteId
    , "Desc" :==>            emit Desc
    , "data" :==>            emit Data
    , "|" :==>               emit Pipe
    , "IDesc" :==>           emit IDesc
    , "“IId”".|. "\"IId\"" :==> emit Quote_IId
    , "“Σ”" .|. "\"Sg\"" :==> emit Quote_Sg
    , "“Π”" .|. "\"Pi\"" :==> emit Quote_Pi
    , "elimID" :==>          emit IDesc_Elim
    , "µI" .|. "muI" :==>    emit MuI
    , "inductionI" :==>      emit InductionI
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
    , "recursionOn" .|. "inductionOn" :==>     emit RecursionOn
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
