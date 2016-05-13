{-# LANGUAGE TypeFamilies, FlexibleContexts, TypeOperators, FlexibleInstances #-}

-- |
-- Module         : Control.FiniteStateMachine
-- Copyright      : (C) Robert Atkey 2013
-- License        : BSD3
--
-- Maintainer     : bob.atkey@gmail.com
-- Stability      : experimental
-- Portability    : unknown
--
-- This module contains a type class capturing finite state machines
-- over arbitrary input alphabets. This class has the following
-- features:
--
-- * When reaching an accepting state, a value may be returned. See
-- the 'isAcceptingState' function.
--
-- * Very large alphabets (e.g., unicode) are supported by means of
-- the 'classes' function.

module Data.FiniteStateMachine
    ( -- * Finite State Machines: definition and simulation
      FiniteStateMachine (..)
    , runFSM
      -- * Combinators for 'FiniteStateMachine's
    , (:==>) (..)
    , Literal (..)
    )
    where

import Data.RangeSet (Partition, fromSet, singleton)
import Data.Maybe (listToMaybe, mapMaybe)

-- | Class of types whose inhabitants represent finite state
-- machines. Members of this type class should be /finite/ state. So
-- there can only be a finite number of possible states reachable from
-- 'initState' via 'advance'. FIXME: mention why this doesn't
-- necessarily mean that the 'State fsm' type is an instance of
-- 'Bounded'.
class ( Ord (State fsm)
      , Eq (State fsm)
      , Enum (Alphabet fsm)
      , Ord (Alphabet fsm)
      , Bounded (Alphabet fsm))
    => FiniteStateMachine fsm where

    -- | The type of states of finite state acceptors of this type.
    data State fsm :: *

    -- | The type of symbols recognised by this type of finite state
    -- acceptor.
    type Alphabet fsm :: *

    -- | The type of results returned by this type of finite state
    -- acceptor on acceptance of an input sequence.
    type Result fsm :: *

    -- | The initial state of a given finite state acceptor of this
    -- type.
    initState :: fsm -> State fsm

    -- | State transition function given an input token from the
    -- alphabet of this finite state acceptor.
    advance :: fsm -> Alphabet fsm -> State fsm -> State fsm

    -- | Determine whether the given state is an accepting state of
    -- the finite state acceptor. If so, return the result value for
    -- this accepting state.
    isAcceptingState :: fsm -> State fsm -> Maybe (Result fsm)

    -- | Returns a partition of the alphabet of this finite state
    -- acceptor such that for each equivalence class in the partition,
    -- it is the case that 'advance fsm c1 s == advance fsm c2
    -- s'. FIXME: explain this better.
    classes :: fsm -> State fsm -> Partition (Alphabet fsm)

--------------------------------------------------------------------------------
-- | Really should be fixed length vectors, but I can't be
-- bothered. FIXME: might be easier with the data kinds stuff.
instance FiniteStateMachine fsm => FiniteStateMachine [fsm] where
    data State [fsm]    = ListFSMState { unListFSMState :: [State fsm] }
    type Alphabet [fsm] = Alphabet fsm
    type Result [fsm]   = Result fsm

    initState fsms =
        ListFSMState (map initState fsms)

    advance fsms c =
        ListFSMState .
        map (\(fsm,s) -> advance fsm c s) .
        zip fsms .
        unListFSMState

    isAcceptingState fsm =
        listToMaybe .
        mapMaybe (uncurry isAcceptingState) .
        zip fsm .
        unListFSMState

    classes fsm =
        foldMap (uncurry classes) . zip fsm . unListFSMState

instance Eq (State fsm) => Eq (State [fsm]) where
    ListFSMState s1 == ListFSMState s2 = s1 == s2

instance Ord (State fsm) => Ord (State [fsm]) where
    compare (ListFSMState s1) (ListFSMState s2) =
        compare s1 s2

--------------------------------------------------------------------------------
-- | A tuple type intended for attaching result values to existing
-- 'FiniteStateMachine's.
data fsm :==> a = fsm :==> a
    deriving (Eq, Ord, Show)

infixr 5 :==>

-- | Attaching results to 'FiniteStateMachine's
instance (FiniteStateMachine fsm) => FiniteStateMachine (fsm :==> a) where
     data State (fsm :==> a)
         = TaggedFSMState { unTaggedFSMState :: State fsm }
     type Alphabet (fsm :==> a) = Alphabet fsm
     type Result (fsm :==> a)   = a

     initState (fsm :==> a) =
         TaggedFSMState $ initState fsm

     advance (fsm :==> a) c =
         TaggedFSMState . advance fsm c . unTaggedFSMState

     isAcceptingState (fsm :==> a) =
         fmap (const a) . isAcceptingState fsm . unTaggedFSMState

     classes (fsm :==> a) =
         classes fsm . unTaggedFSMState

instance Eq (State fsm) => Eq (State (fsm :==> a)) where
    TaggedFSMState s1 == TaggedFSMState s2 = s1 == s2

instance Ord (State fsm) => Ord (State (fsm :==> a)) where
    compare (TaggedFSMState s1) (TaggedFSMState s2) =
        compare s1 s2

--------------------------------------------------------------------------------
-- | Treat a list of items as a 'FiniteStateMachine'. As a
-- 'FiniteStateMachine', @Literal l@ accepts exactly the list of
-- symbols @l@.
newtype Literal a = Literal [a]

-- | Treat a list of items as a 'FiniteStateMachine'. As a
-- 'FiniteStateMachine', @Literal l@ accepts exactly the list of
-- symbols @l@.
instance (Bounded a, Enum a, Ord a) => FiniteStateMachine (Literal a) where
    data State (Literal a)    = Expecting [a]
                              | Error
                                deriving (Eq, Ord)
    type Alphabet (Literal a) = a
    type Result (Literal a)   = ()

    initState (Literal l) = Expecting l

    advance _ c Error          = Error
    advance _ c (Expecting []) = Error
    advance _ c (Expecting (c':cs))
        | c == c'   = Expecting cs
        | otherwise = Error

    isAcceptingState _ (Expecting []) = Just ()
    isAcceptingState _ _              = Nothing

    classes _ Error             = mempty
    classes _ (Expecting [])    = mempty
    classes _ (Expecting (c:_)) = fromSet (singleton c)

--------------------------------------------------------------------------------
-- | Simulate a finite state machine on an input sequence. The input
-- sequence should be finite.
runFSM :: FiniteStateMachine fsm =>
          fsm -- ^ A finite state machine
       -> [Alphabet fsm] -- ^ Input sequence, should be finite
       -> Maybe (Result fsm) -- ^ @Nothing@ if the sequence is not
                             -- accepted by the finite state
                             -- machine. @Just x@ if the whole
                             -- sequence is accepted
runFSM fsm input
    = run (initState fsm) input
    where
      run q []     = isAcceptingState fsm q
      run q (x:xs) = run (advance fsm x q) xs
