{-# LANGUAGE TemplateHaskell #-}

module Language.Foveran.Parsing.Token
    ( Token (..)
    )
    where

import qualified Data.Set as S
import           Language.Forvie.Layout
import           Language.Forvie.Lexing.Spec
import           Language.Haskell.TH.Lift

data Token
    = Assume
    | Ident
    | ConstructorName
    | Colon
    | Semicolon
    | Equals
    | Lambda
    | Arrow
    | LeftArrow
    | LParen
    | RParen
    | Times
    | QuoteTimes
    | Plus
    | Fst
    | Snd
    | Inl
    | Inr
    | QuoteK
    | Construct
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
    | Number
    | Data
    | Normalise
    | Where
    | In

    | Eq
    | Refl
    | ElimEq
    | RewriteBy

    | IDesc
    | Quote_IId
    | Quote_Sg
    | Quote_Pi
    | Bind
    | IDesc_Elim
    | SemI
    | MapI
    | LiftI
    | MuI

    | Generalise
    | CasesOn
    | RecursionOn
    | RecurseOn

    | Group
    | AbGroup
    | GroupUnit
    | GroupInv
    | GroupMul

    | Underscore
    | LSqBracket
    | RSqBracket
    | Then
    | AbsurdBy
    | Hole
    | Eliminate
      deriving (Eq,Ord)

deriveLift ''Token

instance SyntaxHighlight Token where
    lexicalClass Assume      = Keyword
    lexicalClass Ident       = Identifier
    lexicalClass ConstructorName = Constructor
    lexicalClass Colon       = Operator
    lexicalClass Semicolon   = Punctuation
    lexicalClass Equals      = Operator
    lexicalClass Lambda      = Keyword
    lexicalClass Arrow       = Operator
    lexicalClass LeftArrow   = Punctuation
    lexicalClass LParen      = Punctuation
    lexicalClass RParen      = Punctuation
    lexicalClass LSqBracket  = Punctuation
    lexicalClass RSqBracket  = Punctuation
    lexicalClass Times       = Operator
    lexicalClass QuoteTimes  = Constructor
    lexicalClass Plus        = Operator
    lexicalClass Fst         = Keyword
    lexicalClass Snd         = Keyword
    lexicalClass Inl         = Constructor
    lexicalClass Inr         = Constructor
    lexicalClass QuoteK      = Constructor
    lexicalClass Construct   = Constructor
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
    lexicalClass Set         = Type
    lexicalClass EmptyType   = Type
    lexicalClass ElimEmpty   = Keyword
    lexicalClass UnitType    = Type
    lexicalClass Number      = Constant
    lexicalClass Data        = Keyword
    lexicalClass Normalise   = Keyword
    lexicalClass IDesc       = Type
    lexicalClass Quote_IId   = Constructor
    lexicalClass Quote_Sg    = Constructor
    lexicalClass Quote_Pi    = Constructor
    lexicalClass Bind        = Keyword
    lexicalClass IDesc_Elim  = Keyword
    lexicalClass SemI        = Keyword
    lexicalClass MapI        = Keyword
    lexicalClass LiftI       = Keyword
    lexicalClass MuI         = Type
    lexicalClass Eq          = Operator
    lexicalClass Refl        = Constructor
    lexicalClass ElimEq      = Keyword
    lexicalClass RewriteBy   = Keyword
    lexicalClass Generalise  = Keyword
    lexicalClass CasesOn     = Keyword
    lexicalClass RecursionOn = Keyword
    lexicalClass RecurseOn   = Operator
    lexicalClass Where       = Keyword
    lexicalClass In          = Keyword
    lexicalClass Underscore  = Punctuation
    lexicalClass Then        = Keyword
    lexicalClass AbsurdBy    = Keyword
    lexicalClass Hole        = Keyword
    lexicalClass Group       = Keyword
    lexicalClass AbGroup     = Keyword
    lexicalClass GroupUnit   = Operator
    lexicalClass GroupMul    = Operator
    lexicalClass GroupInv    = Operator
    lexicalClass Eliminate   = Keyword

instance Layout Token where
    lbrace = LBrace
    rbrace = RBrace
    semicolon = Semicolon
    blockOpener = S.fromList [Where,With]

instance Show Token where
  show Assume = "assume"
  show Ident  = "<identifier>"
  show ConstructorName = "`<constructor-name>"
  show Colon  = ":"
  show Semicolon   = ";"
  show Equals      = "="
  show Lambda      = "\\"
  show Arrow       = "->"
  show LeftArrow   = "<-"
  show LParen      = "("
  show RParen      = ")"
  show LSqBracket  = "["
  show RSqBracket  = "]"
  show Times       = "×"
  show QuoteTimes  = "“×”"
  show Plus        = "+"
  show Fst         = "fst"
  show Snd         = "snd"
  show Inl         = "inl"
  show Inr         = "inr"
  show QuoteK      = "“K”"
  show Construct   = "construct"
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
  show Number      = "<number>"
  show Data        = "data"
  show IDesc       = "IDesc"
  show Quote_IId   = "“IId”"
  show Quote_Sg    = "“Σ”"
  show Quote_Pi    = "“Π”"
  show Bind        = "bind"
  show IDesc_Elim  = "elimID"
  show SemI        = "semI"
  show MapI        = "mapI"
  show LiftI       = "liftI"
  show MuI         = "µI"
  show Eq          = "=="
  show Refl        = "refl"
  show ElimEq      = "elimEq"
  show RewriteBy   = "rewriteBy"
  show Generalise  = "generalise"
  show CasesOn     = "casesOn"
  show RecursionOn = "recursionOn"
  show RecurseOn   = "recurseOn"
  show Normalise   = "normalise"
  show Where       = "where"
  show In          = "in"
  show Underscore  = "_"
  show Then        = "then"
  show AbsurdBy    = "absurdBy"
  show Hole        = "?"
  show Group       = "Group"
  show AbGroup     = "AbGroup"
  show GroupUnit   = "unit"
  show GroupMul    = "#"
  show GroupInv    = "inv"
  show Eliminate   = "eliminate"
