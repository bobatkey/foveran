module Text.PrettyPrintPrec
    (PrecDoc (),
     fromDoc,
     atPrecedenceLevel,
     resetPrec,
     text,
     empty,
     (<>), (<+>), ($$), hang, nest, hsep, hcat, punctuate, sep, paren, cat, down, vcat,
     int,
     comma,
     render)
    where

import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint (Doc)
import           Data.String

-- FIXME: replicate the rest of the PrettyPrint interface

-- Wrapper to track precedence levels
newtype PrecDoc = PrecDoc { atPrecedenceLevel :: Int -> Doc }

instance IsString PrecDoc where
    fromString s = PrecDoc $ \lev -> PP.text s

fromDoc :: Doc -> PrecDoc
fromDoc d = PrecDoc (const d)

text :: String -> PrecDoc
text s = fromString s

empty :: PrecDoc
empty = PrecDoc $ \_ -> PP.empty

(<>) :: PrecDoc -> PrecDoc -> PrecDoc
p1 <> p2 = PrecDoc $ \lev -> (PP.<>) (p1 `atPrecedenceLevel` lev) (p2 `atPrecedenceLevel` lev)

(<+>) :: PrecDoc -> PrecDoc -> PrecDoc
p1 <+> p2 = PrecDoc $ \lev -> (PP.<+>) (p1 `atPrecedenceLevel` lev) (p2 `atPrecedenceLevel` lev)

($$) :: PrecDoc -> PrecDoc -> PrecDoc
p1 $$ p2 = PrecDoc $ \lev -> (PP.$$) (p1 `atPrecedenceLevel` lev) (p2 `atPrecedenceLevel` lev)

($+$) :: PrecDoc -> PrecDoc -> PrecDoc
p1 $+$ p2 = PrecDoc $ \lev -> (PP.$+$) (p1 `atPrecedenceLevel` lev) (p2 `atPrecedenceLevel` lev)

hang :: PrecDoc -> Int -> PrecDoc -> PrecDoc
hang p1 n p2 = PrecDoc $ \lev -> PP.hang (p1 `atPrecedenceLevel` lev) n (p2 `atPrecedenceLevel` lev)

nest :: Int -> PrecDoc -> PrecDoc
nest n p = PrecDoc $ \lev -> PP.nest n (p `atPrecedenceLevel` lev)

hsep :: [PrecDoc] -> PrecDoc
hsep l = PrecDoc $ \lev -> PP.hsep $ map (`atPrecedenceLevel` lev) l

hcat :: [PrecDoc] -> PrecDoc
hcat l = PrecDoc $ \lev -> PP.hcat $ map (`atPrecedenceLevel` lev) l

sep :: [PrecDoc] -> PrecDoc
sep l = PrecDoc $ \lev -> PP.sep $ map (`atPrecedenceLevel` lev) l

vcat :: [PrecDoc] -> PrecDoc
vcat l = PrecDoc $ \lev -> PP.vcat $ map (`atPrecedenceLevel` lev) l

cat :: [PrecDoc] -> PrecDoc
cat l = PrecDoc $ \lev -> PP.cat $ map (`atPrecedenceLevel` lev) l

punctuate :: PrecDoc -> [PrecDoc] -> [PrecDoc]
punctuate p []     = []
punctuate p [d]    = [d]
punctuate p (d:ds) = (d <> p) : punctuate p ds

paren :: Int -> PrecDoc -> PrecDoc
paren braklev p
    = PrecDoc $ \lev -> if braklev > lev then PP.parens (p `atPrecedenceLevel` braklev) else p `atPrecedenceLevel` braklev

down :: PrecDoc -> PrecDoc
down p = PrecDoc $ \lev -> p `atPrecedenceLevel` (lev - 1)

resetPrec :: PrecDoc -> PrecDoc
resetPrec p = PrecDoc $ \_ -> p `atPrecedenceLevel` 10

int :: Int -> PrecDoc
int i = PrecDoc $ \_ -> PP.int i

comma :: PrecDoc
comma = PrecDoc $ \_ -> PP.comma

render :: PrecDoc -> String
render d = PP.render (d `atPrecedenceLevel` 10)