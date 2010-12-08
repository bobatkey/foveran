{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}

module Foveran.Parsing.Lexer where

import Control.StreamProcessor
import Control.StreamProcessor.Positions
import Data.BooleanAlgebra
import Text.Regexp
import Text.CharacterSet
import Text.LexerGenerator
import Foveran.Parsing.Token

lexer :: LexingError e => SP e Char (Lexeme Token)
lexer = addPositions >>> $(makeStaticLexer
        [ ("assume",          Emit Assume)
        , (":",               Emit Colon)
        , (":=",              Emit ColonEquals)
        , (";",               Emit Semicolon)
        , ("=",               Emit Equals)
        , ("\\" .|. "\x03bb", Emit Lambda)
        , ("->" .|. "→",      Emit Arrow)
        , ("(",               Emit LParen)
        , (")",               Emit RParen)
        , ("“→”",             Emit QuoteArrow)
        , ("×",               Emit Times)
        , ("“×”",             Emit QuoteTimes)
        , ("+",               Emit Plus)
        , ("“+”",             Emit QuotePlus)
        , ("fst",             Emit Fst)
        , ("snd",             Emit Snd)
        , ("inl",             Emit Inl)
        , ("inr",             Emit Inr)
        , ("“K”",             Emit QuoteK)
        , ("µ",               Emit Mu)
        , ("construct",       Emit Construct)
        , ("induction",       Emit Induction)
        , ("elimD",           Emit ElimD)
        , ("()" .|. "⋄",      Emit UnitValue)
        , ("«",               Emit LDoubleAngle)
        , ("»",               Emit RDoubleAngle)
        , (",",               Emit Comma)
        , ("case",            Emit Case)
        , ("for",             Emit For)
        , (".",               Emit FullStop)
        , ("with",            Emit With)
        , ("{",               Emit LBrace)
        , ("}",               Emit RBrace)
        , ("Set",             Emit Set)
        , ("Empty" .|. "𝟘",   Emit EmptyType)
        , ("Unit" .|. "𝟙",    Emit UnitType)
        , ("elimEmpty",       Emit ElimEmpty)
        , ("“Id”",            Emit QuoteId)
        , ("Desc",            Emit Desc)
        , ("data",            Emit Data)
        , ("|",               Emit Pipe)
        , (tok (nameStartChar .&. complement (singleton '\x03bb')) .>>. zeroOrMore (tok nameChar),
                              Emit Ident)
        , (oneOrMore (tok num),
                              Emit Number)
        , (oneOrMore (tok space),
                              Ignore)
        , (("--" .|. "–") .>>. star (tok (complement (singleton '\n'))),
                              Ignore)
        , ("{-"
           .>>.
           (star (tok anyChar) .&. complement (star (tok anyChar) .>>. "-}" .>>. star (tok anyChar)))
           .>>.
           "-}",              Ignore) -- FIXME: allow multiple lexer states to allow nested comments
        ])
