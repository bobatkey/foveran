{-# LANGUAGE TemplateHaskell #-}

module Language.Foveran.Parsing.Token
    ( Token (..)
    )
    where

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