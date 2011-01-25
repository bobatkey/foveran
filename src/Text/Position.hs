module Text.Position where

import Data.Rec

data Position = Position { posCharNum   :: Int
                         , posLineNum   :: Int
                         , posColumnNum :: Int
                         }
              deriving (Eq, Ord, Show)

initPos :: Position
initPos = Position 0 1 0

updatePos :: Position -> Char -> Position
updatePos (Position cnum lnum colnum) '\n' = Position (cnum + 1) (lnum + 1) 0
updatePos (Position cnum lnum colnum) _    = Position (cnum + 1) lnum (colnum + 1)

data Span = Span Position Position
            deriving (Eq, Ord, Show)

class Regioned r where
    posLeft  :: r -> Position
    posRight :: r -> Position

makeSpan :: (Regioned r, Regioned r') => r -> r' -> Span
makeSpan x y = Span (posLeft x) (posRight y)

instance Regioned Span where
  posLeft (Span l _)  = l
  posRight (Span _ r) = r
  
instance Regioned r => Regioned (AnnotRec r f) where
  posLeft (Annot r _) = posLeft r
  posRight (Annot r _) = posRight r
  
instance Regioned r => Regioned [r] where
  posLeft (x:_) = posLeft x
  posRight l    = posRight (last l)