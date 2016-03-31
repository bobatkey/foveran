{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses, FlexibleInstances #-}

module Text.ParserCombinators where

import           Prelude hiding (head)
import           Control.Monad
import           Control.Monad.Error
import           Control.Applicative
import           Text.Lexeme (Lexeme (..))
import           Text.Position
import qualified Data.Text as T
import           Data.MonadicStream hiding (append, toList)

{------------------------------------------------------------------------------}
data Parser tok a
    = Return   a
    | Terminal tok (Lexeme tok -> Parser tok a)
    | EOS                        (Parser tok a)
    | Choice   (Parser tok a)    (Parser tok a)
    | Fail
    | Commit                     (Parser tok a)

instance Monad (Parser tok) where
    return = Return
    Return a     >>= f = f a
    Terminal p k >>= f = Terminal p (\c -> k c >>= f)
    EOS k        >>= f = EOS (k >>= f)
    Choice k1 k2 >>= f = Choice (k1 >>= f) (k2 >>= f)
    Fail         >>= f = Fail
    Commit k     >>= f = Commit (k >>= f)

instance Functor (Parser tok) where
    fmap f p = p >>= return . f

instance Applicative (Parser tok) where
    pure = return
    (<*>) = ap

token :: tok -> Parser tok Span
token t = Terminal t (\(Lexeme _ p _) -> Return p)

tokenWithText :: tok -> Parser tok (T.Text,Span)
tokenWithText t = Terminal t (\(Lexeme _ p s) -> Return (s,p))

eos :: Parser tok ()
eos = EOS (Return ())

instance Alternative (Parser tok) where
    empty = Fail
    (<|>) = Choice

commit :: Parser tok ()
commit = Commit (Return ())

{------------------------------------------------------------------------------}
data StateComponent tok a
    = ExpectingToken tok (Lexeme tok -> Parser tok a)
    | ExpectingEOS                     (Parser tok a)

type State tok a = [StateComponent tok a]
type DState tok a = [StateComponent tok a] -> [StateComponent tok a]

expecting :: State tok a -> [Maybe tok]
expecting = fmap expect
    where expect (ExpectingToken t _) = Just t
          expect (ExpectingEOS _)     = Nothing

cut :: ([a] -> [a]) -> [a] -> [a]
cut l = \x -> l []

parserToStateH :: Parser tok a -> Either a (DState tok a)
parserToStateH (Return a)     = Left a
parserToStateH (Terminal t k) = pure $ (ExpectingToken t k:)
parserToStateH (EOS k)        = pure $ (ExpectingEOS k:)
parserToStateH (Choice k1 k2) = (.) <$> parserToStateH k1 <*> parserToStateH k2
parserToStateH Fail           = pure $ id
parserToStateH (Commit k)     = cut <$> parserToStateH k

advanceH :: Eq tok => State tok a -> Maybe (Lexeme tok) -> Either a (DState tok a)
advanceH [] _ = pure $ id
advanceH (ExpectingToken p k:s) i@(Just t)
    | lexemeTok t == p =
        (.) <$> parserToStateH (k t) <*> advanceH s i
advanceH (ExpectingToken p k:s) i
    = advanceH s i
advanceH (ExpectingEOS k:s) i@(Just _)
    = advanceH s i
advanceH (ExpectingEOS k:s) i@Nothing
    = (.) <$> parserToStateH k <*> advanceH s i

advance :: Eq tok => State tok a -> Maybe (Lexeme tok) -> Either a (State tok a)
advance s i = fmap ($ []) $ advanceH s i

class ParsingError tok e where
    parseError :: Maybe (Lexeme tok) -> [Maybe tok] -> e

instance ParsingError tok String where
    parseError Nothing               _ = "Parse error on EOS"
    parseError (Just (Lexeme _ p s)) _ = "Parser error at " ++ show p ++ " on input '" ++ T.unpack s ++ "'"

parse :: (Eq tok, MonadError e m, ParsingError tok e) => Parser tok a -> Reader (Lexeme tok) m a
parse p = case parserToStateH p of
            Left a  -> return a
            Right s -> go (s [])
    where
      go state = do
        t <- head
        case advance state t of
          Left result  -> return result
          Right []     -> lift $ throwError (parseError t (expecting state))
          Right state' -> go state'
