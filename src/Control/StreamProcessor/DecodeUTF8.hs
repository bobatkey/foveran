{-# LANGUAGE TypeSynonymInstances #-}

module Control.StreamProcessor.DecodeUTF8 where

import Control.StreamProcessor
import Data.Word (Word8)
import Data.Char
import Data.Bits

class UTF8DecodeError e where
  utf8DecodeError :: String -> e

instance UTF8DecodeError String where
  utf8DecodeError s = s

readContinuationByte :: UTF8DecodeError e => (Word8 -> SP e Word8 b) -> SP e Word8 b
readContinuationByte k = Get validate
    where
      validate Nothing  = Error $ utf8DecodeError "Unexpected EOS"
      validate (Just b)
          | b .&. 0xc0 == 0x80 = k b
          | otherwise          = Error $ utf8DecodeError "Bad continuation byte"

decodeTwoByte :: Word8 -> Word8 -> Char
decodeTwoByte b1 b2 = c
    where
      yyy    = fromIntegral (b1 .&. 0x1c) `rotateL` 6 
      yy     = fromIntegral (b1 .&. 0x03) `rotateL` 6
      xxxxxx = fromIntegral (b2 .&. 0x3f)
      c      = chr $ yyy + yy + xxxxxx

decodeThreeByte :: Word8 -> Word8 -> Word8 -> Char
decodeThreeByte b1 b2 b3 = c
    where
      zzzz   = fromIntegral $ (b1 .&. 0x0f) `rotateL` 4
      yyyy   = fromIntegral $ (b2 .&. 0x3c) `rotateR` 2
      yy     = fromIntegral $ (b2 .&. 0x03) `rotateL` 6
      xxxxxx = fromIntegral $ b3 .&. 0x3f
      
      c = chr $ (zzzz + yyyy) * 0x100 + (yy + xxxxxx)

decodeFourByte :: Word8 -> Word8 -> Word8 -> Word8 -> Char
decodeFourByte b1 b2 b3 b4 = c
    where
      www    = fromIntegral $ (b1 .&. 0x07) `rotateL` 2
      zz     = fromIntegral $ (b2 .&. 0x30) `rotateR` 4
      zzzz   = fromIntegral $ (b2 .&. 0x0f) `rotateL` 4
      yyyy   = fromIntegral $ (b3 .&. 0x3c) `rotateR` 2
      yy     = fromIntegral $ (b3 .&. 0x03) `rotateL` 6
      xxxxxx = fromIntegral $ b4 .&. 0x3f
      
      c = chr $   (   www + zz) * 0x10000
                + (zzzz + yyyy) * 0x100
                + (yy + xxxxxx)

{-
onChunks :: SP e Word8 Char -> SP e B.ByteString T.Text
onChunks = go
    where
      go = undefined
      -- Read in a block and run the stream processor over it,
      -- collecting all the characters that are output. When the block
      -- is consumed, output the gathered characters as a piece of
      -- text. Need a cut-off so that we always actually output some
      -- text eventually.
-}

decodeUTF8 :: UTF8DecodeError e => SP e Word8 Char
decodeUTF8 = readChar
    where
      readChar = Get examineByte
      
      examineByte Nothing  = EOS
      examineByte (Just b)
          | b <= 0x7f = Put (chr $ fromIntegral b) readChar
          | b <= 0xbf = Error $ utf8DecodeError "Continuation byte in wrong position" 
          | b <= 0xc1 = Error $ utf8DecodeError "Overlong 2-byte sequence"
          | b <= 0xdf = twobyte b
          | b <= 0xef = threebyte b
          | b <= 0xf4 = fourbyte b
          | otherwise = Error $ utf8DecodeError "Invalid byte"

      twobyte b1 = readContinuationByte $ \b2 ->
                   Put (decodeTwoByte b1 b2) readChar

      threebyte b1 = readContinuationByte $ \b2 ->
                     readContinuationByte $ \b3 ->
                     Put (decodeThreeByte b1 b2 b3) readChar
      
      fourbyte b1 = readContinuationByte $ \b2 ->
                    readContinuationByte $ \b3 ->
                    readContinuationByte $ \b4 ->
                    Put (decodeFourByte b1 b2 b3 b4) readChar
{-# INLINE decodeUTF8 #-}