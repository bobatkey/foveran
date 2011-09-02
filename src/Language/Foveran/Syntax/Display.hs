{-# LANGUAGE DeriveFunctor #-}

module Language.Foveran.Syntax.Display
    ( Ident
    , Definition (..)
    , Datatype (..)
    , Constructor (..)
    , Declaration (..)
    , Term
    , TermPos
    , TermCon (..)
    )
    where

import Language.Foveran.Syntax.Identifier (Ident)
import Text.Position
import Data.Rec

data Definition =
    Definition Span Ident TermPos Ident TermPos

data Datatype =
    Datatype Span Ident [(Ident,TermPos)] [Constructor]

data Declaration
    = AssumptionDecl Span Ident TermPos
    | DefinitionDecl Definition
    | DatatypeDecl   Datatype
    | Normalise      TermPos

type Term = Rec TermCon
type TermPos = AnnotRec Span TermCon

data TermCon tm
    = Var   Ident
    | Lam   [Ident] tm
    | App   tm [tm]
    | Set   Int
    | Pi    [Ident] tm tm
    | Arr   [tm] tm
    | Sigma [Ident] tm tm
    | Prod  tm tm
    | Pair  tm tm
    | Proj1 tm
    | Proj2 tm
    | Sum   tm tm
    | Inl   tm
    | Inr   tm
    | Case  tm Ident tm Ident tm Ident tm
    | Unit
    | UnitI
    | Empty
    | ElimEmpty

    | Eq     tm tm
    | Refl
    | ElimEq tm Ident Ident tm tm

    {- Descriptions of non-indexed types -}
    | Desc
    | Desc_K    tm
    | Desc_Id
    | Desc_Prod tm tm
    | Desc_Sum  tm tm
    | Desc_Elim
    | Sem
    | Mu        tm
    | Construct tm
    | Induction
      
    {- Descriptions of indexed types -}
    | IDesc
    | IDesc_Id   tm
    | IDesc_Sg   tm tm
    | IDesc_Pi   tm tm
    | IDesc_Elim
    | MuI        tm tm
    | InductionI
    deriving (Show, Functor)

data Constructor
    = Constructor Ident [TermPos]
