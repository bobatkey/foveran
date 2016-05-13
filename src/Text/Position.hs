-- |
-- Module             :  Text.Position
-- Copyright          :  (C) Robert Atkey 2013
-- License            :  BSD3
--
-- Maintainer         :  bob.atkey@gmail.com
-- Stability          :  experimental
-- Portability        :  unknown
--
-- Representation of positions within a piece of text for the purposes
-- of error reporting.

module Text.Position
    ( Position (..)
    , initPos
    , updatePos
    , Span (..)
    , Regioned (..)
    , makeSpan )
    where

import Data.ByteString (ByteString)

-- | Representation of a position in a piece of source text.
data Position = Position
    { posSourceName :: {-# UNPACK #-} !ByteString -- ^ Source name, usually a filename
    , posCharNum    :: {-# UNPACK #-} !Int -- ^ Character offset
    , posLineNum    :: {-# UNPACK #-} !Int -- ^ Line number
    , posColumnNum  :: {-# UNPACK #-} !Int -- ^ Column number
    } deriving (Eq, Ord)

instance Show Position where
    show (Position sourceName char line col) =
        "(Position " ++ show sourceName ++ " " ++ show char ++ " " ++ show line ++ " " ++ show col ++ ")"

-- | Initial position at character offset @0@, line number @1@ and
-- column number @0@. Formally, @initPos = Position 0 1 0@.
initPos :: ByteString -> Position
initPos sourceName = Position sourceName 0 1 0

-- | Update a position given an input character. FIXME: justify the
-- newline handling.
updatePos :: Position -> Char -> Position
updatePos (Position src cnum lnum colnum) '\n' = Position src (cnum + 1) (lnum + 1) 0
updatePos (Position src cnum lnum colnum) _    = Position src (cnum + 1) lnum (colnum + 1)

-- | A span covering the region between two positions.
data Span =
    Span !Position !Position
    deriving (Eq, Ord, Show)

-- | Elements of a 'Regioned' type have a left and a right position
-- within some source text.
class Regioned r where
    regionLeft  :: r -> Position
    regionRight :: r -> Position

-- | Generate a 'Span' from a 'Regioned' value using the 'regionLeft'
-- and 'regionRight' positions of that value.
makeSpan :: (Regioned r, Regioned r') => r -> r' -> Span
makeSpan x y = Span (regionLeft x) (regionRight y)

instance Regioned Span where
  regionLeft (Span l _)  = l
  regionRight (Span _ r) = r
