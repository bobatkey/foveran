module Control.StreamProcessor.ByteString where

import           Data.Word
import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as BU
import           Control.StreamProcessor

deChunk :: SP e B.ByteString Word8
deChunk = go
    where
      go = Get handle
      
      handle Nothing  = EOS
      handle (Just s) = loop 0 (B.length s) s
      
      loop n m s
          | n == m    = go
          | otherwise = Put (BU.unsafeIndex s n) (loop (n+1) m s)

{-
onByteString :: B.ByteString -> SP String Word8 a -> [a]
onByteString s = go 0
    where
      length = B.length s
      
      go n (Get k) | n == length = go n (k Nothing)
                   | otherwise   = go (n+1) (k $ Just (BU.unsafeIndex s n))
      go n (Put a k)             = a : go n k
      go n (Error e)             = error e
      go n EOS                   = []
-}
