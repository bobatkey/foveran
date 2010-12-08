{-# LANGUAGE TypeSynonymInstances, TemplateHaskell, FlexibleContexts, TypeFamilies #-}

module Text.LexerGenerator where

import qualified Control.StreamProcessor as SP
import           Control.StreamProcessor.Rewindable
import           Text.Position (Position, Span (Span))
import qualified Text.Regexp.DFA as DFA
import qualified Data.Text as T
import           Text.Regexp.DFATH
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

data Action tok
    = Emit tok
    | Ignore
    deriving (Eq, Ord, Show)

instance Lift tok => Lift (Action tok) where
    lift (Emit tok) = [| Emit $(lift tok) |]
    lift Ignore     = [| Ignore |]

data Lexer tok = Lexer (DFA.DFA (Action tok))

compileLexer :: (Ord tok, DFA.RegexpLike r, DFA.Result r ~ Action tok) => r -> Lexer tok
compileLexer regexps = Lexer (DFA.makeDFA regexps)

class LexingError e where
    lexingErrAtEOS   :: e
    lexingErrOnInput :: Char -> Position -> e

instance LexingError String where
    lexingErrAtEOS = "Lexing error at End of Stream"
    lexingErrOnInput c lexeme = "Lexing error on input " ++ show c ++ "; current lexeme: " ++ show lexeme

{------------------------------------------------------------------------------}
data Lexeme tok = Lexeme { lexemeTok  :: tok
                         , lexemePos  :: Span
                         , lexemeText :: T.Text
                         }
                deriving (Eq, Ord, Show)

{------------------------------------------------------------------------------}
data PartialLexeme = PartialLexeme { pLexemeStart        :: Position
                                   , pLexemeTextReversed :: String
                                   }

addToLexeme Nothing                    c p = PartialLexeme p [c]
addToLexeme (Just (PartialLexeme p s)) c _ = PartialLexeme p (c:s)

completeLexeme (PartialLexeme p s) p' Ignore     = Nothing
completeLexeme (PartialLexeme p s) p' (Emit tok) = Just (Lexeme tok (Span p p') (T.pack $ reverse s))

makeLexer :: (LexingError e, Ord tok) => Lexer tok -> SP.SP e (Char,Position) (Lexeme tok)
makeLexer (Lexer dfa) = rewindableToSP $ go initState
    where
      initState = (0, Nothing, Nothing) -- (DFA state, Partial lexeme, Current match)

      go state = Get $ processInput state

      processInput (_,        Nothing, Nothing) Nothing = EOS
      processInput (_,        Just _,  current) Nothing = emit current Nothing
      processInput (dfaState, lexeme,  current) input@(Just (c,p))
          = let lexeme' = addToLexeme lexeme c p
            in case DFA.transition dfa dfaState c of
                 DFA.Accepting t newState -> Mark $ go (newState, Just lexeme', Just (completeLexeme lexeme' p t))
                 DFA.Error                -> emit current input
                 DFA.Change newState      -> go (newState, Just lexeme', current)

      emit Nothing              Nothing      = Error lexingErrAtEOS
      emit Nothing              (Just (c,p)) = Error $ lexingErrOnInput c p
      emit (Just Nothing)       _            = Rewind $ go initState
      emit (Just (Just lexeme)) _            = Put lexeme $ Rewind $ go initState

makeStaticLexer :: (DFA.RegexpLike r, Ord (DFA.Result r), Lift (DFA.Result r)) => r -> ExpQ
makeStaticLexer spec =
    [| let initState = (0, Nothing, Nothing)

           go state = Get $ processInput state

           processInput (_,        Nothing, Nothing) Nothing = EOS
           processInput (_,        Just _,  current) Nothing = emit current Nothing
           processInput (dfaState, lexeme,  current) input@(Just (c,p))
               = let lexeme' = addToLexeme lexeme c p
                 in case $(makeTransitionFunction dfa) dfaState c of
                      DFA.Accepting t newState -> Mark $ go (newState, Just lexeme', Just (completeLexeme lexeme' p t))
                      DFA.Error                -> emit current input
                      DFA.Change newState      -> go (newState, Just lexeme', current)

           emit Nothing              Nothing      = Error lexingErrAtEOS
           emit Nothing              (Just (c,p)) = Error $ lexingErrOnInput c p
           emit (Just Nothing)       _            = Rewind $ go initState
           emit (Just (Just lexeme)) _            = Put lexeme $ Rewind $ go initState
        in
          rewindableToSP $ go initState
     |]
    where
      dfa = DFA.makeDFA spec
