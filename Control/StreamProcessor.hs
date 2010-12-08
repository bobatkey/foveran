module Control.StreamProcessor where

import System.IO

-- Consider an extension with commands too, like in the old
-- StreamProcessor.hs

data SP e a b = Get (Maybe a -> SP e a b)
              | Error e
              | Put b (SP e a b)
              | EOS

infixr 5 >>>

-- FIXME: consider other stream processor composition operators
(>>>) :: SP e a b -> SP e b c -> SP e a c
Get f    >>> sp2     = Get $ \a -> f a >>> sp2
Error e  >>> sp2     = Error e
Put b k1 >>> Get k2  = k1 >>> k2 (Just b)
EOS      >>> Get k2  = EOS >>> k2 Nothing
sp1      >>> Error e = Error e
sp1      >>> Put c k = Put c (sp1 >>> k)
sp1      >>> EOS     = EOS
{-# INLINE (>>>) #-}

run :: SP String a b -> [a] -> [b]
run (Get k) []     = run (k Nothing) []
run (Get k) (a:as) = run (k (Just a)) as
run (Error e) _    = error $ "error: " ++ e -- FIXME: yes, I know
run (Put b k) as   = b : run k as
run EOS       _    = []

-- this is actually a synchronous stream processor
mapSP :: (a -> b) -> SP e a b
mapSP f = Get $ \a -> case a of
                        Nothing -> EOS
                        Just a  -> Put (f a) (mapSP f)

onHandles :: Handle -> Handle -> SP e Char String -> IO (Maybe e)
onHandles input output = go
    where
      go (Get k)   = do isEOF <- hIsEOF input
                        if isEOF then go (k Nothing) else hGetChar input >>= go . k . Just
      go (Put b k) = do hPutStr output b; go k
      go (Error e) = do return (Just e)
      go EOS       = do return Nothing

onFile :: FilePath -> SP e Char String -> IO (Maybe e)
onFile filename sp = do h <- openFile filename ReadMode
                        result <- onHandles h stdout sp
                        hClose h
                        return result
