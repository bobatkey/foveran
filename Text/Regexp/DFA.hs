{-# LANGUAGE PackageImports, TypeFamilies, FlexibleInstances #-}

-- implementation of the DFA construction algorithm from Owens et al

-- FIXME: make DFA type abstract and provide abstract transition
-- functions. Is there any way to tie the state type to the DFA? Rank
-- 2 polymorphism?

module Text.Regexp.DFA
    ( RegexpLike (..)
    , DFA (..)
    , makeDFA
    , runDFA
    , TransitionResult (..)
    , transition
    )
    where

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import           Data.Array (Array, array, (!))
import           Data.RangeSet
import           Text.CharacterSet
import "mtl"     Control.Monad.State

{------------------------------------------------------------------------------}
-- FIXME: this needs a better name
class Ord r => RegexpLike r where
    type Result r :: *
    diff           :: Char -> r -> r
    matchesNothing :: r -> Bool
    matchesEmpty   :: r -> Maybe (Result r)
    classes        :: r -> S.Set CSet

{------------------------------------------------------------------------------}
-- DFA construction
data ConstructorState re
    = CS { csStates      :: M.Map re Int
         , csNextState   :: Int
         , csTransitions :: IM.IntMap [(CSet,Int)]
         , csErrorStates :: IS.IntSet
         , csFinalStates :: IM.IntMap (Result re)
         }

type ConstructorM re a = State (ConstructorState re) a

haveVisited :: Ord re => re -> ConstructorM re (Maybe Int)
haveVisited r = get >>= return . M.lookup r . csStates

addTransition :: Int -> CSet -> Int -> ConstructorM re ()
addTransition src cl tgt =
    modify $ \s -> s{ csTransitions = IM.alter addT src (csTransitions s) }
    where
      addT Nothing  = Just [(cl,tgt)]
      addT (Just l) = Just ((cl,tgt):l)

-- FIXME: could compress all error states into one?
newState :: RegexpLike re => re -> ConstructorM re Int
newState r =
    do CS states next trans error final <- get
       let states' = M.insert r next states
           next'   = next + 1
           error'  = if matchesNothing r then IS.insert next error else error
           final'  = case matchesEmpty r of
                       Nothing  -> final
                       Just res -> IM.insert next res final
       put (CS states' next' trans error' final')
       return next

-- rework this so that we visit a node, we gather all the outgoing
-- transitions at once and combine them into a single transition table
-- entry

-- Also, want to record the fact that the collection of classes that
-- we get are non-overlapping and cover the whole of the character
-- set.

explore :: RegexpLike re => re -> Int -> ConstructorM re ()
explore q s = mapM_ (goto q s) (S.elems $ classes q)

goto :: RegexpLike re => re -> Int -> CSet -> ConstructorM re ()
goto q s cl =
    case getRepresentative cl of
      Nothing ->
          return ()
      Just c ->
          do let qcn = diff c q
             visited <- haveVisited qcn
             case visited of
               Just s' ->
                   do addTransition s cl s'
               Nothing ->
                   do s' <- newState qcn
                      addTransition s cl s'
                      explore qcn s'

data DFA a = DFA { numStates   :: Int
                 , transitions :: Array Int [(CSet,Int)]
                 , errorStates :: IS.IntSet
                 , finalStates :: IM.IntMap a
                 }
             deriving Show

makeDFA :: RegexpLike re => re -> DFA (Result re)
makeDFA r = DFA next transArray error final
    where
      init = CS (M.fromList [ (r, 0) ]) 1 (IM.fromList []) IS.empty IM.empty

      CS states next trans error final = execState (explore r 0) init

      transArray = array (0,next-1) (IM.assocs trans)

{------------------------------------------------------------------------------}
{- Running DFAs -}
data TransitionResult a
    = Accepting a Int
    | Error
    | Change Int
      deriving (Eq, Ord, Show)

transition :: DFA a -> Int -> Char -> TransitionResult a
transition (DFA _ transitions errorStates acceptingStates) state c = result
    where
      newState = jump (transitions ! state)

      jump []         = error "Non exhaustive jumps"
      jump ((cl,s):l) = if c `memberOf` cl then s else jump l

      result = if IS.member newState errorStates then Error
               else case IM.lookup newState acceptingStates of
                      Nothing -> Change newState
                      Just a  -> Accepting a newState

runDFA :: DFA a -> String -> Maybe a
runDFA dfa = aux 0
    where
      DFA _ transitions _ final = dfa

      aux s []     = IM.lookup s final
      aux s (c:cs) = aux (jump c (transitions ! s)) cs

      jump c []         = error "Non exhaustive jumps"
      jump c ((cl,s):l) = if c `memberOf` cl then s else jump c l
