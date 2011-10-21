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
    | Sem
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
    | Normalise
    | Where

    | Eq
    | Refl
    | ElimEq
    | RewriteBy

    | IDesc
    | Quote_IId
    | Quote_Sg
    | Quote_Pi
    | IDesc_Elim
    | MuI
    | InductionI

    | Underscore
      deriving (Eq,Ord)

deriveLift ''Token

instance SyntaxHighlight Token where
    lexicalClass Assume      = Keyword
    lexicalClass Ident       = Identifier
    lexicalClass Colon       = Operator
    lexicalClass ColonEquals = Operator
    lexicalClass Semicolon   = Punctuation
    lexicalClass Equals      = Operator
    lexicalClass Lambda      = Keyword
    lexicalClass Arrow       = Operator
    lexicalClass LParen      = Punctuation
    lexicalClass RParen      = Punctuation
    lexicalClass QuoteArrow  = Constructor
    lexicalClass Times       = Operator
    lexicalClass QuoteTimes  = Constructor
    lexicalClass Plus        = Operator
    lexicalClass QuotePlus   = Constructor
    lexicalClass Fst         = Keyword
    lexicalClass Snd         = Keyword
    lexicalClass Inl         = Constructor
    lexicalClass Inr         = Constructor
    lexicalClass QuoteK      = Constructor
    lexicalClass Mu          = Keyword
    lexicalClass Construct   = Constructor
    lexicalClass Induction   = Keyword
    lexicalClass ElimD       = Keyword
    lexicalClass UnitValue   = Constructor
    lexicalClass LDoubleAngle= Constructor
    lexicalClass RDoubleAngle= Constructor
    lexicalClass Comma       = Constructor
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
    lexicalClass QuoteId     = Constructor
    lexicalClass Desc        = Keyword
    lexicalClass Number      = Constant
    lexicalClass Pipe        = Punctuation
    lexicalClass Data        = Keyword
    lexicalClass Normalise   = Keyword
    lexicalClass IDesc       = Keyword
    lexicalClass Sem         = Keyword
    lexicalClass Quote_IId   = Constructor
    lexicalClass Quote_Sg    = Constructor
    lexicalClass Quote_Pi    = Constructor
    lexicalClass IDesc_Elim  = Keyword
    lexicalClass MuI         = Keyword
    lexicalClass InductionI  = Keyword
    lexicalClass Eq          = Operator
    lexicalClass Refl        = Constructor
    lexicalClass ElimEq      = Keyword
    lexicalClass RewriteBy   = Keyword
    lexicalClass Where       = Keyword
    lexicalClass Underscore  = Punctuation

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
  show Quote_IId   = "“IId”"
  show Quote_Sg    = "“Σ”"
  show Quote_Pi    = "“Π”"
  show IDesc_Elim  = "elimID"
  show Sem         = "sem"
  show MuI         = "µI"
  show InductionI  = "inductionI"
  show Eq          = "≡"
  show Refl        = "refl"
  show ElimEq      = "elimEq"
  show RewriteBy   = "rewriteBy"
  show Normalise   = "normalise"
  show Where       = "where"
  show Underscore  = "_"
