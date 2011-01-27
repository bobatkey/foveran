{-# LANGUAGE TemplateHaskell #-}

module Language.Foveran.Parsing.Token
    ( Token (..)
    )
    where

import Language.Forvie.Lexing.Spec
import Language.Haskell.TH.Lift

data Token
    = Assume
    | Ident
    | Colon
    | ColonEquals
    | Semicolon
    | Equals
    | Lambda
    | Arrow
    | LParen
    | RParen
    | QuoteArrow
    | Times
    | QuoteTimes
    | Plus
    | QuotePlus
    | Fst
    | Snd
    | Inl
    | Inr
    | QuoteK
    | Mu
    | Construct
    | Induction
    | ElimD
    | UnitValue
    | LDoubleAngle
    | RDoubleAngle
    | Comma
    | Case
    | For
    | FullStop
    | With
    | LBrace
    | RBrace
    | Set
    | EmptyType
    | ElimEmpty
    | UnitType
    | QuoteId
    | Desc
    | Number
    | Pipe
    | Data
      
    | IDesc
    | IDesc_K
    | IDesc_Id
    | IDesc_Pair
    | IDesc_Sg
    | IDesc_Pi
    | IDesc_Elim
      deriving (Eq,Ord)

deriveLift ''Token

instance SyntaxHighlight Token where
    lexicalClass Assume = Keyword
    lexicalClass Ident  = Identifier
    lexicalClass Colon  = Operator
    lexicalClass ColonEquals = Operator
    lexicalClass Semicolon   = Punctuation
    lexicalClass Equals      = Operator
    lexicalClass Lambda      = Keyword
    lexicalClass Arrow       = Operator
    lexicalClass LParen      = Punctuation
    lexicalClass RParen      = Punctuation
    lexicalClass QuoteArrow  = Operator
    lexicalClass Times       = Operator
    lexicalClass QuoteTimes  = Operator
    lexicalClass Plus        = Operator
    lexicalClass QuotePlus   = Operator
    lexicalClass Fst         = Keyword
    lexicalClass Snd         = Keyword
    lexicalClass Inl         = Keyword
    lexicalClass Inr         = Keyword
    lexicalClass QuoteK      = Operator
    lexicalClass Mu          = Keyword
    lexicalClass Construct   = Keyword
    lexicalClass Induction   = Keyword
    lexicalClass ElimD       = Keyword
    lexicalClass UnitValue   = Keyword
    lexicalClass LDoubleAngle= Punctuation
    lexicalClass RDoubleAngle= Punctuation
    lexicalClass Comma       = Punctuation
    lexicalClass Case        = Keyword
    lexicalClass For         = Keyword
    lexicalClass FullStop    = Punctuation
    lexicalClass With        = Keyword
    lexicalClass LBrace      = Punctuation
    lexicalClass RBrace      = Punctuation
    lexicalClass Set         = Keyword
    lexicalClass EmptyType   = Keyword
    lexicalClass ElimEmpty   = Keyword
    lexicalClass UnitType    = Keyword
    lexicalClass QuoteId     = Keyword
    lexicalClass Desc        = Keyword
    lexicalClass Number      = Constant
    lexicalClass Pipe        = Punctuation
    lexicalClass Data        = Keyword
    lexicalClass IDesc       = Keyword
    lexicalClass IDesc_K     = Keyword
    lexicalClass IDesc_Id    = Keyword
    lexicalClass IDesc_Pair  = Keyword
    lexicalClass IDesc_Sg    = Keyword
    lexicalClass IDesc_Pi    = Keyword
    lexicalClass IDesc_Elim  = Keyword

instance Show Token where
  show Assume = "assume"
  show Ident  = "<identifier>"
  show Colon  = ":"
  show ColonEquals = ":=" 
  show Semicolon   = ";"
  show Equals      = "="
  show Lambda      = "\\"
  show Arrow       = "→"
  show LParen      = "("
  show RParen      = ")"
  show QuoteArrow  = "“→”"
  show Times       = "×"
  show QuoteTimes  = "“×”"
  show Plus        = "+"
  show QuotePlus   = "“+”"
  show Fst         = "fst"
  show Snd         = "snd"
  show Inl         = "inl"
  show Inr         = "inr"
  show QuoteK      = "“K”"
  show Mu          = "µ"
  show Construct   = "construct"
  show Induction   = "induction"
  show ElimD       = "elimD"
  show UnitValue   = "()"
  show LDoubleAngle = "«"
  show RDoubleAngle = "»"
  show Comma       = ","
  show Case        = "case"
  show For         = "for"
  show FullStop    = "."
  show With        = "with"
  show LBrace      = "{"
  show RBrace      = "}"
  show Set         = "Set"
  show EmptyType   = "Empty"
  show ElimEmpty   = "elimEmpty"
  show UnitType    = "Unit"
  show QuoteId     = "“Id“"
  show Desc        = "Desc"
  show Number      = "<number>"
  show Pipe        = "|"
  show Data        = "data"
  show IDesc       = "IDesc"
  show IDesc_K     = "'K"
  show IDesc_Id    = "'Id"
  show IDesc_Pair  = "'Pair"
  show IDesc_Sg    = "'Sg"
  show IDesc_Pi    = "'Pi"
  show IDesc_Elim  = "elimID"