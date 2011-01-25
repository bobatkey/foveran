{-# LANGUAGE TypeSynonymInstances #-}

module Control.StreamReader where

import System.IO
import Control.StreamProcessor

{------------------------------------------------------------------------------}
data SR e a b = Read (Maybe a -> SR e a b)
              | ReaderError e
              | Yield b

-- FIXME: would using a right kan extension speed this up?
instance Monad (SR e a) where
    return = Yield
    Read k        >>= f = Read $ \a -> k a >>= f
    ReaderError e >>= f = ReaderError e
    Yield b       >>= f = f b

instance Functor (SR e a) where
    fmap f (Yield a)       = Yield (f a)
    fmap f (ReaderError e) = ReaderError e
    fmap f (Read k)        = Read $ \x -> fmap f $ k x

{------------------------------------------------------------------------------}
class UnexpectedEOSError e where
    unexpectedEOS :: e

instance UnexpectedEOSError String where
    unexpectedEOS = "Unexpected End Of Stream"

readInput :: UnexpectedEOSError e => SR e a a
readInput = Read handle
    where handle Nothing  = ReaderError unexpectedEOS
          handle (Just a) = Yield a

readError :: e -> SR e a b
readError e = ReaderError e

{------------------------------------------------------------------------------}
infixr 4 >>|

(>>|) :: SP e a b -> SR e b c -> SR e a c
Get f    >>| sr            = Read $ \a -> f a >>| sr
Error e  >>| sr            = ReaderError e
Put b k1 >>| Read k2       = k1 >>| k2 (Just b)
EOS      >>| Read k2       = EOS >>| k2 Nothing
sp       >>| ReaderError e = ReaderError e
sp       >>| Yield c       = Yield c
{-# INLINE (>>|) #-}

{------------------------------------------------------------------------------}
gatherer :: SR e a [a]
gatherer = go []
    where
      go l = Read (input l)
      input l Nothing  = Yield (reverse l)
      input l (Just a) = go (a:l)

{------------------------------------------------------------------------------}
-- never stops with EOS?
iterateSR :: SR e a b -> SP e a b
iterateSR sr = go sr
    where
      go (Read k)        = Get $ go . k
      go (ReaderError e) = Error e
      go (Yield b)       = Put b $ go sr

{------------------------------------------------------------------------------}
onList :: [a] -> SR e a b -> Either e b
onList = go
    where
      go []     (Read k)        = go [] (k Nothing)
      go (a:as) (Read k)        = go as (k (Just a))
      go as     (ReaderError e) = Left e
      go as     (Yield b)       = Right b
