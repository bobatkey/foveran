{-# LANGUAGE TemplateHaskell,
             OverloadedStrings,
             TypeSynonymInstances,
             FlexibleInstances,
             RankNTypes #-}

module Language.Foveran.Parsing.Layout
    ( NewlineOr (..)
    , Layout (..)
    , LayoutErrorHandler (..)
    , layout

    , WithLayout (..)
    , insertLayout
    , computeLayout
    )
    where

import           Language.Foveran.Lexing.Spec (SyntaxHighlight (..), Classification (..))
import           Text.Lexeme
import           Text.Position
import           Data.MonadicStream
import           Language.Haskell.TH.Syntax
import qualified Data.Set as S

-- Do an implementation of layout as per the Haskell standard:
--  http://www.haskell.org/onlinereport/syntax-iso.html

-- See also:
--  http://www.bitc-lang.org/docs/bitc/layout.html

-- 1. A processor that produces the stream expected by the layout algorithm
-- 2. The context-sensitive layout processor

-- Ignore "Note 5" about recovering from parse errors, because it is wicked

-- This algorithm isn't shy about inserting semicolons, so the
-- downstream parser should be able to cope with empty bits between semicolons

-- FIXME: document the position information that appears in the synthetic lexemes

data NewlineOr tok
    = Token tok
    | Newline
    deriving (Ord, Eq, Show)

instance Lift tok => Lift (NewlineOr tok) where
    lift (Token tok) = [| Token $(lift tok) |]
    lift Newline     = [| Newline |]

instance SyntaxHighlight tok => SyntaxHighlight (NewlineOr tok) where
    lexicalClass (Token t) = lexicalClass t
    lexicalClass Newline   = Whitespace

--------------------------------------------------------------------------------
zeroWidthSpan :: Span -> Span
zeroWidthSpan (Span l _) = Span l l

--------------------------------------------------------------------------------
class Ord tok => Layout tok where
    lbrace      :: tok
    rbrace      :: tok
    semicolon   :: tok
    blockOpener :: S.Set tok

isBlockOpener :: (Ord tok, Layout tok) => tok -> Bool
isBlockOpener tok = S.member tok blockOpener

--------------------------------------------------------------------------------
data WithLayout a
    = LLexeme     (Lexeme a)
    | IndentCurly Span Int
    | IndentAngle Span Int
    deriving Show

-- IndentCurly means "I want to start a new block with indentation level 'n'"
-- IndentAngle means "This line has indentation level 'n', please work out what block it should be in"

{------------------------------------------------------------------------------}
data LayoutState
    = Normal
    | AfterBlockOpen
    | AfterNewline

layoutHelper :: (Ord tok, Layout tok) =>
                LayoutState
             -> Lexeme (NewlineOr tok)
             -> (LayoutState, [WithLayout tok])
layoutHelper Normal         (Lexeme Newline   _ _) =
    ( AfterNewline
    , [] )
layoutHelper Normal         (Lexeme (Token t) p s) =
    ( if isBlockOpener t then AfterBlockOpen else Normal
    , [LLexeme (Lexeme t p s)] )
layoutHelper AfterBlockOpen (Lexeme Newline   _ _) =
    ( AfterBlockOpen
    , [] )
layoutHelper AfterBlockOpen (Lexeme (Token t) p s) =
    if t == lbrace then
        (Normal, [LLexeme (Lexeme t p s)])
    else
        ( if isBlockOpener t then AfterBlockOpen else Normal
        , [ IndentCurly (zeroWidthSpan p) (posColumnNum (regionLeft p) + 1)
          , LLexeme (Lexeme t p s) ] )
layoutHelper AfterNewline   (Lexeme Newline   _ _) =
    ( AfterNewline
    , [] )
layoutHelper AfterNewline   (Lexeme (Token t) p s) =
    ( if isBlockOpener t then AfterBlockOpen else Normal
    , [ IndentAngle (zeroWidthSpan p) (posColumnNum (regionLeft p) + 1)
      , LLexeme (Lexeme t p s) ] )

layoutEOS :: LayoutState -> [WithLayout a]
layoutEOS Normal         = []
layoutEOS AfterBlockOpen = [IndentCurly (Span (initPos "") (initPos "")) 0]
layoutEOS AfterNewline   = []

insertLayout :: (Layout tok, Ord tok, Monad m) =>
                Processor (Lexeme (NewlineOr tok)) m (WithLayout tok)
insertLayout = concatMapAccum layoutHelper layoutEOS AfterBlockOpen

{------------------------------------------------------------------------------}
newtype LayoutErrorHandler m =
    OnLayoutError { onError :: forall a. Span -> m a }

-- FIXME: why these strings?
semicolonLexeme, lbraceLexeme, rbraceLexeme :: Layout tok => Span -> Lexeme tok
semicolonLexeme p = Lexeme semicolon p ";"
lbraceLexeme p = Lexeme lbrace p "{"
rbraceLexeme p = Lexeme rbrace p "}"

prependLexeme :: Lexeme tok
              -> ([Int], [Lexeme tok])
              -> ([Int], [Lexeme tok])
prependLexeme l (ms,ls) = (ms,l:ls)

equaliseIndentation :: Layout tok =>
                       Span
                    -> Int
                    -> [Int]
                    -> ( [Int], [Lexeme tok] )
equaliseIndentation p n [] = ( [], [] )
equaliseIndentation p n (m:ms)
    | m == n    = ( m:ms, [semicolonLexeme p] )
    | n < m     = prependLexeme (rbraceLexeme p) (equaliseIndentation p n ms)
    | otherwise = ( m:ms, [] )

-- This is invoked when we see an rbrace on the input. We pop the
-- stack of layout blocks until we reach a user-delimited block. An
-- alternative would be to strictly require that all the layout blocks
-- have been closed by indentation before the user inserted rbrace.
closeUntilUserBlock :: (Monad m, Layout tok) =>
                       LayoutErrorHandler m
                    -> Lexeme tok
                    -> [Int]
                    -> m ([Int], [Lexeme tok])
closeUntilUserBlock h l []     = onError h (lexemePos l)
closeUntilUserBlock h l (0:ms) = return ( ms, [l] )
closeUntilUserBlock h l (n:ms) = do
  output <- closeUntilUserBlock h l ms
  return $ prependLexeme (rbraceLexeme (lexemePos l)) output

computeLayoutHelper :: (Layout tok, Monad m) =>
                       LayoutErrorHandler m
                    -> [Int]
                    -> WithLayout tok
                    -> m ([Int], [Lexeme tok])
computeLayoutHelper h ms     (IndentAngle p n) =
    return (equaliseIndentation p n ms)
computeLayoutHelper h ms     (IndentCurly p n) =
    case ms of
      (m:ms) | n > m  -> return (n:m:ms, [lbraceLexeme p])
      []     | n > 0  -> return ([n],    [lbraceLexeme p])
      ms              -> return (prependLexeme (lbraceLexeme p) $
                                 prependLexeme (rbraceLexeme p) $
                                 equaliseIndentation p n ms)
computeLayoutHelper h ms     (LLexeme l)
    | lexemeTok l == rbrace = closeUntilUserBlock h l ms
    | lexemeTok l == lbrace = return ( 0:ms, [l] )
    | otherwise             = return ( ms, [l] )

computeLayoutEOS :: (Layout tok, Monad m) =>
                    LayoutErrorHandler m
                 -> [Int]
                 -> m [Lexeme tok]
computeLayoutEOS _ []     = return []
computeLayoutEOS h (0:ms) =
    onError h (Span (initPos "") (initPos "")) -- FIXME: better position
computeLayoutEOS h (m:ms) = do
  r <- computeLayoutEOS h ms
  let l = rbraceLexeme (Span (initPos "") (initPos "")) -- FIXME: better position
  return (l:r)

computeLayout :: (Layout tok, Monad m) =>
                 LayoutErrorHandler m
              -> Processor (WithLayout tok) m (Lexeme tok)
computeLayout errorHandler =
    concatMapAccumM (computeLayoutHelper errorHandler)
                    (computeLayoutEOS errorHandler)
                    []
                    
{------------------------------------------------------------------------------}
layout :: (Layout tok, Monad m) =>
          LayoutErrorHandler m
       -> Processor (Lexeme (NewlineOr tok)) m (Lexeme tok)
layout errorHandler = insertLayout >>> computeLayout errorHandler
