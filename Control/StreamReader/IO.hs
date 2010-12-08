module Control.StreamReader.IO where

import Control.StreamReader
import qualified Data.ByteString as B
import System.IO

-- FIXME: handle IO errors somehow

onHandle :: Handle -> Int -> SR e B.ByteString a -> IO (Either e a)
onHandle h bufSize = go
    where
      go (Read k)        = do s <- B.hGet h bufSize
                              if B.null s then go (k Nothing)
                                          else go (k (Just s))
      go (ReaderError e) = return $ Left e
      go (Yield a)       = return $ Right a
{-# INLINE onHandle #-}

onFile :: FilePath -> Int -> SR e B.ByteString a -> IO (Either e a)
onFile filename bufSize sr =
    do h <- openFile filename ReadMode
       result <- onHandle h bufSize sr
       hClose h
       return result
