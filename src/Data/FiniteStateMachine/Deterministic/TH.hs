{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}

-- FIXME: haddock header

module Data.FiniteStateMachine.Deterministic.TH
    (makeTransitionFunction)
    where

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import           Data.Array (assocs)
import           Data.FiniteStateMachine.Deterministic (TransitionResult (..))
import qualified Data.FiniteStateMachine.Deterministic as DFA
import           Data.RangeSet hiding (assocs)
import qualified Data.RangeSet as RS
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

-- convert DFAs to functions that execute them

-- plan is to generate a massive pattern match on the state and the
-- input character. This will return the result as a
-- "TransitionResult"

makeTransitionFunction :: forall c a. (Lift c, Lift a) => DFA.DFA c a -> ExpQ
makeTransitionFunction dfa
    = lamE [ varP state, varP c ]
           (caseE (varE state) (map mkMatch $ assocs transitions))
      where
        _initState = DFA.initialState dfa
        transitions = DFA.transitions dfa
        errorStates = DFA.errorStates dfa
        acceptingStates = DFA.acceptingStates dfa

        mkMatch (q, trans) = match (litP (IntegerL $ fromIntegral q))
                                   (guardedB $ map mkCharMatch $ flattenCSets $ RS.assocs trans)
                                   []

        c = mkName "c"
        state = mkName "state"

        mkCharMatch :: (c, c, Q Exp) -> Q (Guard, Exp)
        mkCharMatch (low, high, res) = normalGE [| $(varE c) >= low && $(varE c) <= high |] res

        mkResult q =
            if q `IS.member` errorStates then [| Error |]
            else case IM.lookup q acceptingStates of
                   Nothing -> [| Change q |]
                   Just a  -> [| Accept a q |]

        flattenCSets = concat . map flattenCSet 
            where
              flattenCSet (cset, q) = let res = mkResult q in map (\(low,high) -> (low, high, res)) (ranges cset)
