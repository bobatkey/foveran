module Language.Foveran.Util.Templater where

import           Prelude hiding (foldl, lex)
import           Control.Monad.Identity (runIdentity)
import           Data.Char (ord)
import           Data.Word (Word8)
import qualified Data.Map as M
import qualified Data.RangeSet as RS
import qualified Data.FiniteStateMachine.Deterministic as DFA
import qualified Data.ByteString as B
import           Data.MonadicStream ((|>|), foldl)
import           Language.Foveran.Lexing.Spec
import           Language.Foveran.Lexing.ByteString

data Token = Text | Variable deriving (Show, Eq, Ord)

dollar :: Word8
dollar = fromInteger $ toInteger $ ord '$'

dollarS :: RS.Set Word8
dollarS = singleton dollar

alphaNum :: RS.Set Word8
alphaNum = interval cA cZ .|. interval ca cz .|. interval c0 c9
    where cA = fromInteger $ toInteger $ ord 'A'
          cZ = fromInteger $ toInteger $ ord 'Z'
          ca = fromInteger $ toInteger $ ord 'a'
          cz = fromInteger $ toInteger $ ord 'z'
          c0 = fromInteger $ toInteger $ ord '0'
          c9 = fromInteger $ toInteger $ ord '9'

dfa :: DFA.DFA Word8 Token
dfa = DFA.dfaOfFSM
      [ tok dollarS .>>. oneOrMore (tok alphaNum) .>>. tok dollarS :==> Variable
      , oneOrMore (tok (complement dollarS))                       :==> Text
      , tok dollarS                                                :==> Text
      ]

dropDollars :: B.ByteString -> B.ByteString
dropDollars =
    B.takeWhile (/=dollar) . B.dropWhile (==dollar)

-- FIXME: use blaze-builder to generate a lazy bytestring
-- or generate a stream of objects, and then use chunksTo
applyVariableSubstitution :: [(B.ByteString, B.ByteString)]
                          -> B.ByteString
                          -> B.ByteString
applyVariableSubstitution substitution input =
    runIdentity (lex dfa (OnError $ return Text) input |>| foldl processChunk mempty)
    where
      substMap = M.fromList substitution

      processChunk d (Variable, s) =
          let s' = dropDollars s in
          case M.lookup s' substMap of
            Nothing -> d `mappend` s'
            Just t  -> d `mappend` t
      processChunk d (Text,     s) =
          d `mappend` s
