{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators #-}

-- |
-- Module      : Language.Foveran.Lexing.Spec
-- Copyright   : Robert Atkey 2012
-- License     : BSD3
--
-- Maintainer  : bob.atkey@gmail.com
-- Stability   : experimental
-- Portability : unknown
--
-- Specification of the lexical structure of programming
-- languages.
--
-- Lexical Structure is specified using a list of regular expressions,
-- which are used to break up the input text from left to right,
-- applying the longest match rule and favouring regular expressions
-- earlier in the list in case of a tie. Each regular expression has
-- an attached semantic token which is used to tag the resulting
-- lexeme.

module Language.Foveran.Lexing.Spec
    ( -- * Example
      -- $example

      -- * Specification of Lexical Structure
      LexicalSpecification
    , (:==>) (..)
      
    -- ** Exported Modules
    -- | The "Data.Regexp" module is re-exported from this module for
    -- convenience when building 'LexicalSpecification's. For regular
    -- expressions over characters, as used here, "Data.Regexp"
    -- provides a 'Data.IsString' instance, which can be used with the
    -- @OverloadedStrings@ pragma to make specifications easier to
    -- read and write.
    , module Data.FiniteStateMachine.RegexpDerivatives

    -- | The "Data.CharSet" module provides several useful predefined
    -- sets of characters for use in 'LexicalSpecification's.
    , module Data.CharSet
      
      -- * Compilation
    , CompiledLexSpec
    , compileLexicalSpecification
    , lexSpecDFA
      
      -- * Useful Token Types
    , Classification (..)
    , SyntaxHighlight (..)
    , Action (..)
    )
    where

import           Language.Haskell.TH.Syntax
import           Data.FiniteStateMachine
import qualified Data.FiniteStateMachine.Deterministic as DFA
import           Data.FiniteStateMachine.RegexpDerivatives
import           Data.CharSet

-- $example
-- FIXME: do an example

-- | A 'LexicalSpecification' represents the specification of the
-- lexical structure of a language.
--
-- A specification consists of a list of regular expressions (of type
-- 'Regexp') each with an associated semantic value.
type LexicalSpecification tok = [Regexp Char :==> tok]


-- | A rough classification of lexemes, used for syntax highlighting.
data Classification
    = Comment      -- ^ Comments
    | Keyword      -- ^ A keyword of the language
    | Identifier   -- ^ An identifier of the language
    | Punctuation  -- ^ Punctuation, such as parentheses or colons
    | Whitespace   -- ^ Whitespace: spaces, tabs, newlines
    | Constant     -- ^ Constants, usually strings and integers
    | Operator     -- ^ Usually infix operators
    | Constructor  -- ^ Constructors of data
    | Type         -- ^ Names of types
    deriving (Eq, Ord, Show)

instance Lift Classification where
    lift Comment     = [| Comment |]
    lift Keyword     = [| Keyword |]
    lift Identifier  = [| Identifier |]
    lift Punctuation = [| Punctuation |]
    lift Whitespace  = [| Whitespace |]
    lift Operator    = [| Operator |]
    lift Constant    = [| Constant |]
    lift Constructor = [| Constructor |]
    lift Type        = [| Type |]

-- | Instances of this class are able to classify themselves into a
-- specific 'Classification' for the purposes of syntax highlighting.
class SyntaxHighlight tok where
    lexicalClass :: tok -> Classification

instance SyntaxHighlight Classification where
    lexicalClass = id

-- | Lexical tokens for programming languages can usually be split
-- into two broad classifications: tokens that are meaningful for
-- programs, like keywords and identifiers, and those like whitespace
-- and comments that are not meaningful. This type provides a way to
-- tag tokens according to these classes. It is then easy to filter
-- these out later on before parsing takes place.
--
-- Ignored tokens are given a 'Classification' in order to facilitate
-- syntax highlighting.
data Action tok
    = Emit   tok -- ^ Meaningful tokens.
    | Ignore Classification -- ^ Other tokens, with a classification.
    deriving (Eq, Ord, Show)

instance SyntaxHighlight tok => SyntaxHighlight (Action tok) where
    lexicalClass (Emit tok)   = lexicalClass tok
    lexicalClass (Ignore typ) = typ

instance Lift tok => Lift (Action tok) where
    lift (Emit tok)   = [| Emit $(lift tok) |]
    lift (Ignore typ) = [| Ignore $(lift typ) |]

-- | The 'CompiledLexSpec' type represents a lexical specification
-- that has been compiled into a DFA (Deterministic Finite Automaton).
newtype CompiledLexSpec tok
    = LS { -- | Extract the DFA (Deterministic Finite Automaton) from a compiled lexical specification.
           lexSpecDFA :: DFA.DFA Char tok
      }

-- | Compile a lexical structure specification into a DFA
-- (Deterministic Finite Automaton).
--
-- Note that this compilation step can be relatively expensive, so it
-- is recommended to ensure that all uses of a compiled lexer
-- specification are shared so that the compilation step is only
-- executed once.
compileLexicalSpecification :: Ord tok => LexicalSpecification tok -> CompiledLexSpec tok
compileLexicalSpecification regexps = LS $ DFA.dfaOfFSM regexps
