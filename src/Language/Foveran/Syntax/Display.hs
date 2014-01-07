{-# LANGUAGE DeriveFunctor #-}

module Language.Foveran.Syntax.Display
    ( Ident

    , Declaration (..)

    , AssumeDecl (..)
    , Definition (..)

    , IDataDecl (..)
    , DataParameter (..)
    , IConstructor (..)
    , IConstructorBitsPos
    , IConstructorBitsCon (..)

    , Pattern (..)
    , Term
    , TermPos
    , TermCon (..)
    )
    where

import Language.Foveran.Syntax.Identifier (Ident)
import Text.Position (Span)
import Data.Pair
import Data.Rec

--------------------------------------------------------------------------------
data Declaration
    = AssumptionDecl AssumeDecl
    | DefinitionDecl Definition
    | IDataDecl      IDataDecl
    | Normalise      TermPos

--------------------------------------------------------------------------------
data AssumeDecl =
    Assume { assumePos   :: Span
           , assumeIdent :: Ident
           , assumeTerm  :: TermPos
           }

--------------------------------------------------------------------------------
data Definition =
    Definition { defnPos   :: Span
               , defnName  :: Ident
               , defnType  :: TermPos
               , defnName2 :: Ident
               , defnArgs  :: [Pattern]
               , defnTerm  :: TermPos
               }

--------------------------------------------------------------------------------
data IDataDecl =
    IData { dataPos          :: Span
          , dataName         :: Ident
          , dataParameters   :: [DataParameter]
          , dataIndexType    :: Maybe TermPos
          , dataConstructors :: [IConstructor]
          }

data DataParameter =
    DataParameter { paramPos   :: Span
                  , paramIdent :: Ident
                  , paramType  :: TermPos
                  }

data IConstructor =
    IConstructor { consPos  :: Span
                 , consName :: Ident
                 , consBits :: IConstructorBitsPos
                 }

type IConstructorBitsPos = AnnotRec Span IConstructorBitsCon

data IConstructorBitsCon x
    = ConsPi  Ident TermPos x
    | ConsArr TermPos x
    | ConsEnd Ident [TermPos]

--------------------------------------------------------------------------------
type Term = Rec TermCon
type TermPos = AnnotRec Span TermCon

data Pattern
    = PatVar   Ident
    | PatTuple [Pattern]
    | PatNull
    deriving (Show)

data TermCon tm
    = Var   Ident
    | Lam   [Pattern] tm
    | App   tm [tm]
    | Set   Int
    | Pi    [([Pattern], tm)] tm
    | Sigma [Pattern] tm tm
    | Prod  tm tm
    | Tuple [tm]
    | Proj1 tm
    | Proj2 tm
    | Sum   tm tm
    | Inl   tm
    | Inr   tm
    | Case  tm (Maybe (Ident, tm)) Pattern tm Pattern tm
    | Unit
    | UnitI
    | Empty
    | ElimEmpty tm (Maybe tm)

    | Eq     tm tm
    | Refl
    | ElimEq tm (Maybe (Ident, Ident, tm)) tm

    {- Descriptions of indexed types -}
    | Construct tm
    | Desc_K    tm
    | Desc_Prod tm tm
    | IDesc
    | IDesc_Id   tm
    | IDesc_Sg   tm tm
    | IDesc_Pi   tm tm
    | IDesc_Elim
    | IDesc_Bind tm Pattern tm
    | SemI       tm Pattern tm
    | MapI       tm Pattern tm Pattern tm tm tm
    | LiftI      tm Pattern tm Pattern Pattern tm tm
    | MuI        tm tm
    | Eliminate  tm (Maybe (Pattern, Pattern, tm)) Pattern Pattern Pattern tm

    | NamedConstructor Ident [tm]
    | CasesOn          Bool tm [(Ident, [Pattern], tm)]
    | RecurseOn        Ident

    | Generalise  tm tm
    | TypeAscrip  tm tm

    | LabelledType Ident [Pair tm] tm
    | Return       tm
    | Call         tm

    | UserHole
    | Hole       Ident [tm]
    deriving (Show, Functor)
