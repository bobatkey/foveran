-- |
-- Module      :  Data.FiniteStateMachine.Deterministic.Elisp
-- Copyright   :  (C) Robert Atkey 2013
-- License     :  BSD3
--
-- Maintainer  :  bob.atkey@gmail.com
-- Stability   :  experimental
-- Portability :  unknown
--
-- FIXME: document the elisp that is produced.

module Data.FiniteStateMachine.Deterministic.Elisp
    ( makeTransitionFunctionCharTables )
    where

import           Data.Array (assocs, range, bounds)
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import           Data.RangeSet (ranges)
import qualified Data.RangeSet as RS
import           Data.Char (ord)
import           Data.Maybe (mapMaybe)
import           Data.SExpr
import qualified Data.FiniteStateMachine.Deterministic as DFA

-- | Turn the DFA into a collection of 'char-table's, one for each
-- state, plus a vector containing all these char-tables
makeTransitionFunctionCharTables :: ShowSExpr a =>
                                    String
                                 -> DFA.DFA Char a
                                 -> [SExpr]
makeTransitionFunctionCharTables prefix dfa =
    [ SExpr [ Atom "defconst"
            , Atom (prefix ++ "-transition-vector")
            , SExpr ([ Atom "let", SExpr letBindings ]
                     ++
                     concatMap charTableEntries (assocs transitions)
                     ++ 
                     [ SExpr (Atom "vector":map (Atom . charTableName) (range $ bounds transitions))
                     ])
            ]
    , SExpr [ Atom "defun"
            , Atom (prefix ++ "-transition-function")
            , SExpr [ Atom "state", Atom "char" ]
            , SExpr [ Atom "aref"
                    , SExpr [ Atom "aref"
                            , Atom (prefix ++ "-transition-vector")
                            , Atom "state"
                            ]
                    , Atom "char"
                    ]
            ]
    ]
    where
      transitions = DFA.transitions dfa
      errorStates = DFA.errorStates dfa
      acceptingStates = DFA.acceptingStates dfa

      charTableName q = "s-" ++ show q

      letBindings = map makeLetBinding $ range $ bounds transitions
          where makeLetBinding q = SExpr [ Atom (charTableName q)
                                         , SExpr [ Atom "make-char-table"
                                                 , Atom "'lexer-table"
                                                 , SExpr [ Atom "list", Atom "'error" ]
                                                 ]
                                         ]
                                                

      charTableEntries (q,trans) =
          map (makeCharTableEntry (charTableName q)) (flattenCSets $ RS.assocs trans)

      makeCharTableEntry name (low,high,res)
          | low == high = SExpr [ Atom "set-char-table-range"
                                , Atom name
                                , IntConst (ord high)
                                , res ]
          | otherwise   = SExpr [ Atom "set-char-table-range"
                                , Atom name
                                , SExpr [ Atom "cons", IntConst (ord low), IntConst (ord high) ]
                                , res
                                ]

      mkResult q =
        if q `IS.member` errorStates then Nothing -- SExpr [ Atom "list", Atom "'error" ]
        else case IM.lookup q acceptingStates of
               Nothing -> Just $ SExpr [ Atom "list", Atom "'change", IntConst q ]
               Just t  -> Just $ SExpr [ Atom "list", Atom "'accept", IntConst q, showSExpr t ]
                           
      flattenCSets = concat . mapMaybe flattenCSet 
          where
            flattenCSet (cset, q) = do
              res <- mkResult q
              return $ map (\(low,high) -> (low, high, res)) (ranges cset)
