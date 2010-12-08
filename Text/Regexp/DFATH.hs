{-# LANGUAGE TemplateHaskell #-}

module Text.Regexp.DFATH where

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import           Data.Array (Array, array, assocs)
import           Text.Regexp.DFA
import           Data.RangeSet
import           Text.CharacterSet
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

-- convert DFAs to functions that execute them

-- plan is to generate a massive pattern match on the state and the
-- input character. This will return the result as a
-- "TransitionResult"

makeTransitionFunction :: Lift a => DFA a -> ExpQ
makeTransitionFunction (DFA numStates transitions errorStates acceptingStates)
    = lamE [ varP state, varP c ]
           (caseE (varE state) (map mkMatch $ assocs transitions))
      where
        mkMatch (q, trans) = match (litP (IntegerL $ fromIntegral q))
                                   (guardedB $ map mkCharMatch $ flattenCSets trans)
                                   []

        c = mkName "c"
        state = mkName "state"

        mkCharMatch (low, high, res) = normalGE [| $(varE c) >= low && $(varE c) <= high |] res

        mkResult q =
            if q `IS.member` errorStates then [| Error |]
            else case IM.lookup q acceptingStates of
                   Nothing -> [| Change q |]
                   Just a  -> [| Accepting a q |]

        flattenCSets = concat . map flattenCSet 
            where
              flattenCSet (cset, q) = let res = mkResult q in map (\(low,high) -> (low, high, res)) (ranges cset)
