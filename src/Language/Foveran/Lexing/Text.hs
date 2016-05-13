-- |
-- Module         : Language.Foveran.Lexing.Text
-- Copyright      : Robert Atkey 2012
-- License        : BSD3
--
-- Maintainer     : bob.atkey@gmail.com
-- Stability      : experimental
-- Portability    : unknown
--
-- Functions for turning `Data.Text.Text` into a stream of lexemes,
-- according to some lexical specification.

module Language.Foveran.Lexing.Text
    ( lex
    , ErrorHandler (..) )
    where

import           Prelude hiding (lex)
import           Data.ByteString (ByteString)
import qualified Data.Text as T
import           Data.MonadicStream (Stream (..), StreamStep (..))
import qualified Data.FiniteStateMachine.Deterministic as DFA
import           Language.Foveran.Lexing.Spec (CompiledLexSpec (..))
import           Text.Lexeme (Lexeme (..))
import           Text.Position (Span (Span), initPos, updatePos, Position)

{------------------------------------------------------------------------------}
data PositionWith a = (:-) { positionOf :: Position
                           , dataOf     :: a
                           }

uncons :: PositionWith T.Text  -> Maybe (PositionWith Char, PositionWith T.Text)
uncons (position :- text) =
    case T.uncons text of
      Nothing       -> Nothing
      Just (c,rest) -> Just ( position                 :- c
                            , (position `updatePos` c) :- rest)

{------------------------------------------------------------------------------}
data CurrentLexeme tok
    = CurrentLexeme { curLexemeText  :: !(PositionWith T.Text)
                    , curLexemeLen   :: !Int
                    , curLexemeMatch :: !(CurrentMatch tok)
                    }

data CurrentMatch tok
    = NoMatch
    | Match !Int !tok !Position !(PositionWith T.Text)

advance :: CurrentLexeme tok -> CurrentLexeme tok
advance lexeme = lexeme { curLexemeLen = curLexemeLen lexeme + 1 }

(+.) :: CurrentLexeme tok -> (PositionWith tok, PositionWith T.Text) -> CurrentLexeme tok
lexeme +. (pos :- tok, rest) =
    lexeme { curLexemeMatch = Match (curLexemeLen lexeme) tok pos rest }

initLexeme :: PositionWith T.Text -> CurrentLexeme tok
initLexeme text = CurrentLexeme text 0 NoMatch

{------------------------------------------------------------------------------}
data ErrorHandler m tok = OnError { onError :: Maybe (Char, Position) -> m tok }

{------------------------------------------------------------------------------}
{-
data State tok
    = BeforeLexeme !(PositionWith T.Text)
    | InLexeme     !Int !(CurrentLexeme tok) !(PositionWith T.Text)

step :: State tok -> m (Maybe (State tok, Lexeme tok))
step (BeforeLexeme text) = undefined
step (InLexeme q lexeme text) = undefined
-}

{------------------------------------------------------------------------------}
lex :: (Ord tok, Monad m) =>
       CompiledLexSpec tok
    -> ErrorHandler m tok
    -> ByteString
    -> T.Text
    -> Stream m (Lexeme tok)
lex lexSpec errorHandler sourceName text =
    go (initPos sourceName :- text)
    where
      dfa = lexSpecDFA lexSpec
      
      go text =
          Stream $ beforeLexeme text

      beforeLexeme text =
          case uncons text of
            Nothing   -> return StreamEnd
            Just step -> onChar (DFA.initialState dfa) step (initLexeme text)

      inLexeme dfaState lexeme text =
          case uncons text of
            Nothing   -> emit lexeme Nothing
            Just step -> onChar dfaState step lexeme

      onChar q input@(position :- c, rest) lexeme =
          case DFA.transition dfa q c of
            DFA.Accept t q' -> inLexeme q' (advance lexeme +. (position :- t, rest)) rest
            DFA.Error       -> emit lexeme (Just input)
            DFA.Change q'   -> inLexeme q' (advance lexeme) rest

      emit lexeme input =
          case curLexemeMatch lexeme of
            NoMatch ->
                do let input' = case input of Nothing -> Nothing; Just (p :- c, _) -> Just (c,p)
                   tok <- errorHandler `onError` input'
                   return (StreamElem (Lexeme tok span text) $ go rest)
                where
                  endPos = case input of
                             Nothing          -> positionOf $ curLexemeText lexeme -- FIXME: this is wrong!
                             Just (p :- _, _) -> p
                  rest   = case input of
                             Nothing        -> initPos sourceName :- T.empty -- FIXME
                             Just (_, rest) -> rest
                  length = curLexemeLen lexeme + case input of Nothing -> 0; Just _ -> 1
                  span   = Span (positionOf $ curLexemeText lexeme) endPos
                  text   = T.take length (dataOf $ curLexemeText lexeme)
            Match length tok endPos rest ->
                return (StreamElem (Lexeme tok span text) $ go rest)
                where
                  span = Span (positionOf $ curLexemeText lexeme) endPos
                  text = T.take length (dataOf $ curLexemeText lexeme)
