{-# LANGUAGE TupleSections #-}

module Language.Foveran.Parsing.Parser
    ( file )
    where

import           Control.Applicative
import           Data.Maybe
import           Data.Rec
import           Text.ParserCombinators
import           Text.Position
import qualified Data.Text as T
import qualified Language.Foveran.Parsing.Token as Tok
import           Language.Foveran.Syntax.Display
import           Language.Foveran.NameSupply (Ident)

{------------------------------------------------------------------------------}
binary f t1 t2 = Annot (makeSpan t1 t2) (f t1 t2)

unary :: (TermPos -> TermCon TermPos) -> Span -> TermPos -> TermPos
unary f p t = Annot (makeSpan p t) (f t)

keyword :: TermCon TermPos -> Span -> TermPos
keyword c s = Annot s c

leftDelimited f p x y = Annot (makeSpan p y) (f x y)

delimited p1 c p2 = Annot (makeSpan p1 p2) c

optBinary t1 Nothing           = t1
optBinary t1 (Just (conn, t2)) = binary conn t1 t2

{------------------------------------------------------------------------------}

number :: Parser Tok.Token (Int,Span)
number = (\(x,y) -> (read $ T.unpack x,y)) <$> tokenWithText Tok.Number

identifier :: Parser Tok.Token Ident
identifier = fst <$> tokenWithText Tok.Ident

identifierList :: Parser Tok.Token [Ident]
identifierList = (:) <$> identifier <*> identifierList
                 <|>
                 pure []

file :: Parser Tok.Token [Declaration]
file = declarations <* eos

declaration :: Parser Tok.Token Declaration
declaration =
    (\p nm t p' -> AssumptionDecl (makeSpan p p') nm t)
        <$> token Tok.Assume
        <*  commit
        <*> identifier
        <*  token Tok.Colon
        <*> term
        <*> token Tok.Semicolon
    <|>
    (\(nm1,p) t1 (nm2,p2) nms t2 p' ->
         DefinitionDecl $ Definition (makeSpan p p') nm1 t1 nm2 (case nms of [] -> t2; nms -> Annot (makeSpan p2 t2) (Lam nms t2)))
        <$> tokenWithText Tok.Ident <* commit <* token Tok.Colon  <*> term <*  token Tok.Semicolon
        <*> tokenWithText Tok.Ident                       
        <*> identifierList
        <* token Tok.Equals <*> term <*> token Tok.Semicolon
    <|>
    (\p nm params constructors p' ->
         DatatypeDecl $ Datatype (makeSpan p p') nm params constructors)
        <$> token Tok.Data
        <*  commit
        <*> identifier
        <*> dataParamList
        <*  token Tok.Colon
        <*  token Tok.Set
        <*  token Tok.ColonEquals
        <*> constructorList
        <*> token Tok.Semicolon

dataParamList :: Parser Tok.Token [(Ident,TermPos)]
dataParamList =
    (\nm t params -> (nm, t) : params)
        <$  token Tok.LParen
        <*  commit
        <*> identifier
        <*  token Tok.Colon
        <*> term
        <*  token Tok.RParen
        <*> dataParamList
    <|>
    pure []

constructorList :: Parser Tok.Token [Constructor]
constructorList =
    (\nm elems constructors -> Constructor nm elems : constructors)
        <$  token Tok.Pipe
        <*  commit
        <*> identifier
        <*  token Tok.Colon
        <*> many term00
        <*> constructorList
    <|>
    pure []

declarations :: Parser Tok.Token [Declaration]
declarations =
    (:) <$> declaration <*> declarations
    <|>
    pure []

term :: Parser Tok.Token TermPos
term = term10

term10 :: Parser Tok.Token TermPos
term10 =
    leftDelimited Lam <$> token Tok.Lambda <* commit <*> identifierList <* token Tok.FullStop <*> term10
    <|>
    (\p idents t1 con t2 -> Annot (makeSpan p t2) (con idents t1 t2))
       <$> token Tok.LParen
       <*> identifierList
       <*  token Tok.Colon
       <*  commit
       <*> term10
       <*  token Tok.RParen
       <*> (Pi <$ token Tok.Arrow <|> Sigma <$ token Tok.Times)
       <*> term10
    <|>
    -- anonymous Pi/function types
    -- right associative
    optBinary <$> term09 <*> optional ((Arr,) <$ token Tok.Arrow <*> term10)

term09 :: Parser Tok.Token TermPos
term09 =
    -- sum types, and their descriptions
    -- right associative
    optBinary <$> term08 <*> (optional $ (Sum,) <$ token Tok.Plus <*> term09
                                         <|>
                                         (Desc_Sum,) <$ token Tok.QuotePlus <*> term09)

term08 :: Parser Tok.Token TermPos
term08 =
    -- product types
    -- right associative
    optBinary <$> term01 <*> (optional $ (Prod,) <$ token Tok.Times <*> term08  
                                         <|>
                                         (Desc_Prod,) <$ token Tok.QuoteTimes <*> term08)

term01 :: Parser Tok.Token TermPos
term01 =
    -- left injection
    unary Inl <$> token Tok.Inl <*> term00
    <|>
    -- right injection
    unary Inr <$> token Tok.Inr <*> term00
    <|>
    -- constant functor descriptions
    unary Desc_K <$> token Tok.QuoteK <*> term00
    <|>
    -- µ
    unary Mu <$> token Tok.Mu <*> term00
    <|>
    -- function application
    -- left associative
    (\t ts -> case ts of [] -> t
                         ts -> binary App t ts) <$> term00 <*> many term00

term00 :: Parser Tok.Token TermPos
term00 =
    unary Proj1 <$> token Tok.Fst <* commit <*> term00
    <|>
    unary Proj2 <$> token Tok.Snd <* commit <*> term00
    <|>
    keyword Construct <$> token Tok.Construct
    <|>
    keyword Induction <$> token Tok.Induction
    <|>
    keyword Desc_Elim <$> token Tok.ElimD
    <|>
    keyword UnitI <$> token Tok.UnitValue
    <|>
    -- FIXME: extend the left and right positions of the term to include the parens
    token Tok.LParen *> term10 <* token Tok.RParen
    <|>
    delimited <$> token Tok.LDoubleAngle <* commit <*> (Pair <$> term10 <* token Tok.Comma <*> term10) <*> token Tok.RDoubleAngle
    <|>
    delimited <$> token Tok.Case
              <* commit
              <*> (Case <$> term10
                        <* token Tok.For <*> identifier <* token Tok.FullStop <*> term10 <* token Tok.With
                        <* token Tok.LBrace
                        <* token Tok.Inl <*> identifier <* token Tok.FullStop <*> term10
                        <* token Tok.Semicolon
                        <* token Tok.Inr <*> identifier <* token Tok.FullStop <*> term10)
              <*> token Tok.RBrace
    <|>
    (\p x -> case x of Nothing     -> Annot p (Set 0)
                       Just (l,p') -> Annot (makeSpan p p') (Set l)) <$> token Tok.Set <*> optional number
    <|>
    keyword Empty <$> token Tok.EmptyType
    <|>
    keyword ElimEmpty <$> token Tok.ElimEmpty
    <|>
    keyword Unit <$> token Tok.UnitType
    <|>
    keyword Desc_Id <$> token Tok.QuoteId
    <|>
    keyword Desc <$> token Tok.Desc
    <|>
    keyword IDesc <$> token Tok.IDesc
    <|>
    keyword IDesc_K <$> token Tok.IDesc_K
    <|>
    keyword IDesc_Id <$> token Tok.IDesc_Id
    <|>
    keyword IDesc_Pair <$> token Tok.IDesc_Pair
    <|>
    keyword IDesc_Sg <$> token Tok.IDesc_Sg
    <|>
    keyword IDesc_Pi <$> token Tok.IDesc_Pi
    <|>
    keyword IDesc_Elim <$> token Tok.IDesc_Elim
    <|>
    (\(nm,p) -> Annot p (Var nm)) <$> tokenWithText Tok.Ident
