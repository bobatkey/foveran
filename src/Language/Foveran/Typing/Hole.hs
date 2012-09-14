{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Typing.Hole
    ( HoleContext
    , HoleGoal (..)
    , HoleData
    , getHoleContext
    , getHoleGoal
    , makeHole
    , ppHole
    , Holes (getHoles)
    , noHoles
    , extendWithHole
    , lookupHole
    )
    where

import           Text.PrettyPrint

import           Language.Foveran.Syntax.Identifier (Ident, UsesIdentifiers (..), runNameGenerationWith)
import           Language.Foveran.Syntax.Checked (Term, bindFree, toDisplaySyntax)
import           Language.Foveran.Parsing.PrettyPrinter
import           Language.Foveran.Typing.LocalContext
import           Language.Foveran.Typing.Conversion.Value (Value, reifyTypeForDisplay)
import qualified Data.Set as S

--------------------------------------------------------------------------------
type HoleContext = [(Ident, Term)]
data HoleGoal    = GoalIsType
                 | GoalType   Term

data HoleData
    = HoleData { holeContext :: HoleContext
               , holeGoal    :: HoleGoal
               }

getHoleContext :: HoleData -> HoleContext
getHoleContext = holeContext

getHoleGoal :: HoleData -> HoleGoal
getHoleGoal = holeGoal

makeHole :: LocalContext -> Maybe Value -> HoleData
makeHole localContext goal =
    HoleData (go members) holeGoal
    where
      members = localContextMembers localContext

      holeGoal = case goal of
                   Nothing -> GoalIsType
                   Just t  -> GoalType (bindFree (map fst members) (reifyTypeForDisplay t) 0)

      go []                       = []
      go ((ident,v):localContext) =
          let holeContext = go localContext
              ty          = bindFree (map fst holeContext) (reifyTypeForDisplay v) 0
          in (ident,ty):holeContext

--------------------------------------------------------------------------------
-- Pretty printing of holes
ppHole :: UsesIdentifiers names => names -> Ident -> HoleData -> Doc
ppHole names holeIdentifier hole =
    "?" <> ppIdent holeIdentifier <> ":"
    <+> "[" <> sep [ sep (punctuate "," (reverse $ ppHoleContextMembers $ holeContext hole))
                   , "|-"
                   , ppHoleGoal (holeGoal hole) ] <> "]"
    where
      ppHoleContextMembers [] = []
      ppHoleContextMembers ((ident, ty):xs) =
          (ppIdent ident <+> ":" <+> ppTerm (map fst xs) ty):ppHoleContextMembers xs

      ppHoleGoal GoalIsType    = "Type"
      ppHoleGoal (GoalType ty) = ppTerm (map fst $ holeContext hole) ty

      ppTerm localNames = ppPlain . runNameGenerationWith names localNames . toDisplaySyntax

-- want it to look like:
--     x : type1
--     y : type2
--     ...
--- |- typeGoal or Type

--------------------------------------------------------------------------------
-- FIXME: need a better representation, instead of association lists
data Holes = Holes { getHoles :: [(Ident, HoleData)] }

noHoles :: Holes
noHoles = Holes []

instance UsesIdentifiers Holes where
    usedIdentifiers = S.fromList . map fst . getHoles

-- FIXME: make this compute what the name of the holes should be
extendWithHole :: Ident -> HoleData -> Holes -> Holes
extendWithHole ident holeData (Holes holes) = Holes ((ident, holeData):holes)

lookupHole :: Ident -> Holes -> HoleData
lookupHole identifier (Holes holes) =
    case lookup identifier holes of
      Nothing       -> error $ "internal error: hole '" ++ show identifier ++ "' not found"
      Just holeData -> holeData