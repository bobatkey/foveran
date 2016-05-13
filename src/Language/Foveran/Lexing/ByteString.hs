-- |
-- Module         : Language.Foveran.Lexing.ByteString
-- Copyright      : Robert Atkey 2012
-- License        : BSD3
--
-- Maintainer     : bob.atkey@gmail.com
-- Stability      : experimental
-- Portability    : unknown
--
-- Functions for turning `Data.ByteString.ByteString` into a stream of
-- lexemes, according to some lexical specification.

module Language.Foveran.Lexing.ByteString
    ( lex
    , ErrorHandler (..) )
    where

import           Prelude hiding (lex)
import           Data.MonadicStream (Stream (..), StreamStep (..))
import           Data.Word (Word8)
import qualified Data.FiniteStateMachine.Deterministic as DFA
import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as BU

data CurrentLexeme tok
    = CurrentLexeme { curLexemePos   :: !Int
                    , curLexemeLen   :: !Int
                    , curLexemeMatch :: !(CurrentMatch tok)
                    }

data CurrentMatch tok
    = NoMatch
    | Match !Int !tok

advance :: CurrentLexeme tok -> CurrentLexeme tok
advance lexeme = lexeme { curLexemeLen = curLexemeLen lexeme + 1 }

(+.) :: CurrentLexeme tok -> tok -> CurrentLexeme tok
lexeme +. tok = lexeme { curLexemeMatch = Match (curLexemeLen lexeme) tok }

initLexeme :: Int -> CurrentLexeme tok
initLexeme pos = CurrentLexeme pos 0 NoMatch

newtype ErrorHandler m tok = OnError { onError :: m tok }

lex :: (Ord tok, Monad m) =>
       DFA.DFA Word8 tok
    -> ErrorHandler m tok
    -> B.ByteString
    -> Stream m (tok, B.ByteString)
lex dfa errorHandler string = go 0
    where
      length = B.length string

      go pos =
          Stream $ beforeLexeme pos

      beforeLexeme pos
          | pos == length = return StreamEnd
          | otherwise     = onChar (DFA.initialState dfa) pos (initLexeme pos)

      inLexeme q lexeme pos
          | pos == length = emit lexeme Nothing
          | otherwise     = onChar q pos lexeme

      onChar q pos lexeme =
          let c = BU.unsafeIndex string pos in
          case DFA.transition dfa q c of
            DFA.Accept t q' -> inLexeme q' (advance lexeme +. t) (pos + 1)
            DFA.Error       -> emit lexeme (Just c)
            DFA.Change q'   -> inLexeme q' (advance lexeme) (pos + 1)

      emit lexeme input =
          let startPos = curLexemePos lexeme in
          case curLexemeMatch lexeme of
            NoMatch ->
                do tok <- onError errorHandler
                   return (StreamElem (tok, substring) $ go (startPos + length))
                where
                  length    = curLexemeLen lexeme + (case input of Nothing -> 0; Just _ -> 1)
                  substring = BU.unsafeTake length (BU.unsafeDrop startPos string)
            Match length tok ->
                return (StreamElem (tok, substring) $ go (startPos + length))
                where
                  substring = BU.unsafeTake length (BU.unsafeDrop startPos string)
