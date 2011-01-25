module Text.PrettyPrint.IsString where

import Text.PrettyPrint
import Data.String

instance IsString Doc where
    fromString = text
