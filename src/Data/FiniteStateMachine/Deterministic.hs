{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE RecursiveDo       #-}

-- |
-- Module           :  Data.FiniteStateMachine.Deterministic
-- Copyright        :  (C) Robert Atkey 2013
-- License          :  BSD3
--
-- Maintainer       :  bob.atkey@gmail.com
-- Stability        :  experimental
-- Portability      :  unknown
--
-- Representation, simulation and construction of Deterministic Finite
-- Automata (DFAs).
--
-- This module uses the 'TotalMap' type from "Data.RangeSet" to
-- represent the transition functions for each state. This can provide
-- a compact representation even when the alphabet of the DFA is
-- large, e.g. all Unicode codepoints.
--
-- Construction of DFA is usually done by using the 'makeDFA'
-- function. This takes values of types that can be treated as
-- deterministic finite state machines and constructs a concrete
-- finite state machine with the same behaviour. The algorithm used is
-- an abstraction of the one presented by Owens et al in /Regular
-- expression derivatives re-examined/ (FIXME: proper reference).
--
-- The DFAs represented here have explicit representation of error
-- states. An error state is a state from which an accepting state can
-- never be reached. Explicit representation of error states is needed
-- when using DFAs for gathering longest matches when scanning text to
-- determine lexemes.
--
-- FIXME: write more about the difference between 'DFA's and
-- 'FiniteStateMachine's.

module Data.FiniteStateMachine.Deterministic
    ( -- * Representation
      DFA
    , initialState
    , transitions
    , errorStates
    , acceptingStates
      
      -- * Constructon of 'DFA's
    , DFAConstruction ()
    , toDFA
    , addState
    , addFinalState
    , fromFSM
    , dfaOfFSM

      -- * Simulation
    , TransitionResult (..)
    , transition )
    where

import           Data.Maybe (maybeToList)
import qualified Data.Map as M
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import           Data.Array (Array, array, (!))
import           Data.RangeSet (TotalMap, ($@), domainPartition, makeTotalMapA, assocs)
import           Control.Applicative (liftA)
import           Control.Monad.Fix (MonadFix (..))
import qualified Control.Monad.State as S
import           Control.Monad.State (modify, gets, execState, join, unless, lift, ap)
import           Data.FiniteStateMachine (FiniteStateMachine (..))

-- | The 'DFA' type has two parameters, the type of input tokens 'a'
-- and the type @b@ of output values attached to accepting
-- states. FIXME: rewrite this to mention 'deterministic finite
-- automaton'
--
-- The states of a DFA are represented as 'Int' values in the range
-- '[0..n]', where 'n' is the number of states of the
-- automaton. State '0' is always the initial state.
data DFA alphabet result = DFA
    { -- | Initial state number
      initialState   :: !Int
    -- | Transition functions of the DFA, indexed by state number.
    , transitions :: !(Array Int (TotalMap alphabet Int))
    -- | The set of error states. Transitions from states in this set
    -- will always lead back to this set, and never to an accepting
    -- state.
    , errorStates :: !IS.IntSet
    -- | The set of accepting states, with attached values.
    , acceptingStates :: !(IM.IntMap result)
    } deriving (Eq, Show)

-- | DFAs are finite state machines.
instance (Enum alphabet, Bounded alphabet, Ord alphabet) =>
    FiniteStateMachine (DFA alphabet result) where
    data State (DFA alphabet result) =
        DFAState { unDFAState :: Int } deriving (Eq, Ord)
    type Alphabet (DFA alphabet result) = alphabet
    type Result (DFA alphabet result)   = result

    initState dfa = DFAState (initialState dfa)

    advance dfa a q = DFAState $ (transitions dfa ! unDFAState q) $@ a

    isAcceptingState dfa q = IM.lookup (unDFAState q) (acceptingStates dfa)

    classes dfa q = domainPartition (transitions dfa ! unDFAState q)

-- | Transform the result values of a DFA.
instance Functor (DFA alphabet) where
    fmap f dfa =
        dfa { acceptingStates = fmap f (acceptingStates dfa) }

{------------------------------------------------------------------------------}
data PartialDFA alphabet result = PartialDFA
    { partNextState   :: !Int
    , partTransitions :: (IM.IntMap (TotalMap alphabet Int))
    , partAccepting   :: !(IM.IntMap result)
    , partBackEdges   :: (IM.IntMap [Int])
    }

initialPartialDFA :: PartialDFA alphabet result
initialPartialDFA = PartialDFA 0 IM.empty IM.empty IM.empty

partialDFAToDFA :: PartialDFA alphabet result
                -> Int
                -> DFA alphabet result
partialDFAToDFA partialDFA initState =
    DFA initState transitions errorStates acceptingStates
    where
      maxState =
          partNextState partialDFA-1

      transitions =
          array (0, maxState) (IM.assocs (partTransitions partialDFA))

      acceptingStates =
          partAccepting partialDFA

      acceptingReaching =
          findAllReachable (partBackEdges partialDFA) (IM.keys acceptingStates)

      errorStates =
          IS.fromList $ filter (\i -> not (IS.member i acceptingReaching)) [0..maxState]

-- Determines the set of reachable states from a given state using the
-- provided edges. This function is used to discover which states are
-- unrecoverable error states in generated automata.
findReachable :: IM.IntMap [Int] -> Int -> IS.IntSet
findReachable edges s = execState (go s) IS.empty
    where
      go s = do
        visited <- gets (IS.member s)
        unless visited $ do
          modify (IS.insert s)
          mapM_ go (join $ maybeToList $ IM.lookup s edges)

-- Uses 'findReachable' to determine the set of states reachable from
-- a list of states. This function is used to discover which states
-- are unrecoverable error states in generated automata.
findAllReachable :: IM.IntMap [Int] -> [Int] -> IS.IntSet
findAllReachable edges = foldMap (findReachable edges)

--------------------------------------------------------------------------------
newtype DFAConstruction s alphabet result a = DFAConstruction
    { unDFAConstruction :: PartialDFA alphabet result
                        -> (PartialDFA alphabet result, a) }

newtype St s = St { unSt :: Int }

instance Functor (DFAConstruction s alphabet result) where
    fmap = liftA

instance Applicative (DFAConstruction s alphabet result) where
    pure = return
    (<*>) = ap

instance Monad (DFAConstruction s alphabet result) where
    return a =
        DFAConstruction $ \pDFA -> (pDFA, a)
    DFAConstruction c >>= f =
        DFAConstruction $ \pDFA ->
            let (pDFA', a) = c pDFA
            in unDFAConstruction (f a) pDFA'

instance MonadFix (DFAConstruction s alphabet result) where
    mfix f =
        DFAConstruction $ \pDFA ->
            let (pDFA', a) = unDFAConstruction (f a) pDFA
            in (pDFA', a)

insertBackEdges :: Int -> IM.IntMap [Int] -> [Int] -> IM.IntMap [Int]
insertBackEdges src =
    foldr (\tgt -> IM.insertWith (++) tgt [src])

addStateInternal :: Ord alphabet =>
                    Maybe result
                 -> TotalMap alphabet (St s)
                 -> DFAConstruction s alphabet result (St s)
addStateInternal maybeResult transitions =
    DFAConstruction $ \pDFA ->
        let thisState = partNextState pDFA
        in ( pDFA { partNextState = thisState+1
                  , partTransitions =
                    IM.insert thisState (unSt <$> transitions)
                          (partTransitions pDFA)
                  , partAccepting =
                    case maybeResult of
                      Nothing -> partAccepting pDFA
                      Just result ->
                          IM.insert thisState result
                                (partAccepting pDFA)
                  , partBackEdges =
                    insertBackEdges thisState
                          (partBackEdges pDFA)
                          (map (unSt . snd) (assocs transitions))
                  }
           , St thisState )

addState :: Ord alphabet =>
            TotalMap alphabet (St s)
         -> DFAConstruction s alphabet result (St s)
addState = addStateInternal Nothing

addFinalState :: Ord alphabet =>
                 result
              -> TotalMap alphabet (St s)
              -> DFAConstruction s alphabet result (St s)
addFinalState result = addStateInternal (Just result)

toDFA :: (forall s. DFAConstruction s alphabet result (St s))
      -> DFA alphabet result
toDFA dfaConstruction = partialDFAToDFA partialDFA initState
    where
      (partialDFA, St initState) =
          unDFAConstruction dfaConstruction initialPartialDFA

{------------------------------------------------------------------------------}
-- FIXME: support for rerouting the accepting states
fromFSM :: FiniteStateMachine fsm =>
           fsm
        -> DFAConstruction s (Alphabet fsm) (Result fsm) (St s)
fromFSM fsm = S.evalStateT (exploreFSM fsm (initState fsm)) M.empty

type Explorer s fsm a =
    S.StateT (M.Map (State fsm) (St s))
             (DFAConstruction s (Alphabet fsm) (Result fsm))
             a

exploreFSM :: FiniteStateMachine fsm =>
              fsm
           -> State fsm
           -> Explorer s fsm (St s)
exploreFSM fsm fsmState = do
  visited <- gets (M.lookup fsmState)
  case visited of
    Just s -> return s
    Nothing -> do
        rec modify (M.insert fsmState s)
            t <- makeTotalMapA (\c -> exploreFSM fsm (advance fsm c fsmState))
                               (classes fsm fsmState)
            s <- lift $ addStateInternal (isAcceptingState fsm fsmState) t
        return s

{------------------------------------------------------------------------------}
dfaOfFSM :: FiniteStateMachine fsm => fsm -> DFA (Alphabet fsm) (Result fsm)
dfaOfFSM fsm = toDFA (fromFSM fsm)

{------------------------------------------------------------------------------}
-- | Representation of the result of stepping a 'DFA'.
data TransitionResult a
    = Accept a !Int
    | Error
    | Change !Int
    deriving (Eq, Ord, Show)

-- | Step a 'DFA' in a given state on a given input. If an error state
-- is reached, then this fact is returned instead of the actual state
-- name.
transition :: Ord a =>
              DFA a b -- ^ a deterministic finite automaton
           -> Int -- ^ state number
           -> a -- ^ input token
           -> TransitionResult b -- ^ the result of this transition
transition dfa state c = result
    where
      DFA _ transitions errorStates acceptingStates = dfa
      
      newState = (transitions ! state) $@ c

      result = if IS.member newState errorStates then Error
               else case IM.lookup newState acceptingStates of
                      Nothing -> Change newState
                      Just a  -> Accept a newState
