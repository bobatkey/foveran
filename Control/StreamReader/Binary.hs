module Control.StreamReader.Binary where

import Data.Functor
import Control.StreamReader
import Data.Word

readWord8 :: UnexpectedEOSError e => SR e Word8 Word8
readWord8 = readInput

readWord32BE :: UnexpectedEOSError e => SR e Word8 Word32
readWord32BE =
    do b1 <- fromIntegral <$> readWord8
       b2 <- fromIntegral <$> readWord8
       b3 <- fromIntegral <$> readWord8
       b4 <- fromIntegral <$> readWord8
       return (b1 * 0x1000000 + b2 * 0x10000 + b3 * 0x100 + b4)

readWord32LE :: UnexpectedEOSError e => SR e Word8 Word32
readWord32LE =
    do b1 <- fromIntegral <$> readWord8
       b2 <- fromIntegral <$> readWord8
       b3 <- fromIntegral <$> readWord8
       b4 <- fromIntegral <$> readWord8
       return (b4 * 0x1000000 + b3 * 0x10000 + b2 * 0x100 + b1)

readWord16BE :: UnexpectedEOSError e => SR e Word8 Word16
readWord16BE =
    do b1 <- fromIntegral <$> readWord8
       b2 <- fromIntegral <$> readWord8
       return (b1 * 0x100 + b2)

