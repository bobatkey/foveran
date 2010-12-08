module Control.StreamProcessor.Positions where

import Text.Position
import Control.StreamProcessor

addPositions :: SP e Char (Char,Position)
addPositions = go initPos
    where
      go pos = Get (handleInput pos)

      handleInput pos Nothing  = EOS
      handleInput pos (Just c) = Put (c,pos) (go (pos `updatePos` c))
