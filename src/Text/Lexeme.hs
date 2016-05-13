-- |
-- Module             :  Text.Lexeme
-- Copyright          :  (C) Robert Atkey 2013
-- License            :  BSD3
--
-- Maintainer         :  bob.atkey@gmail.com
-- Stability          :  experimental
-- Portability        :  unknown
--
-- Representation of lexemes, pieces of text tagged with semantic
-- tokens.

module Text.Lexeme
    ( Lexeme(..) )
    where

import qualified Data.Text as T
import           Text.Position (Span, Regioned (..))

-- | A lexeme is an annotated piece of text from a larger body of
-- text, consisting of three parts:
data Lexeme token = Lexeme
    { lexemeTok  :: !token  -- ^ The token assigned to this lexeme
    , lexemePos  :: !Span   -- ^ The position of this lexeme in the source
    , lexemeText :: !T.Text -- ^ The actual text of this lexeme
    } deriving (Eq, Ord, Show)

-- | The region occupied by a 'Lexeme' is the region of the underlying
-- 'lexemePos'.
instance Regioned (Lexeme token) where
    regionLeft  = regionLeft . lexemePos
    regionRight = regionRight . lexemePos
