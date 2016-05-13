-- |
-- Module      : Data.SExpr
-- Copyright   : Robert Atkey 2010
-- License     : BSD3
--
-- Maintainer  : bob.atkey@gmail.com
-- Stability   : experimental
-- Portability : unknown
--
-- Simple representation of S-expressions, and pretty printing
-- thereof. Mainly used for generation of Emacs Lisp code.

module Data.SExpr
    ( SExpr (..)
    , ShowSExpr (showSExpr)
    , cond
    , pprint
    )
    where

import Text.PrettyPrint

class ShowSExpr a where
    showSExpr :: a -> SExpr

data SExpr = Atom     String
           | IntConst Int
           | SExpr    [SExpr]

instance ShowSExpr SExpr where
    showSExpr = id

cond :: [(SExpr, SExpr)] -> SExpr
cond clauses = SExpr (Atom "cond" : map (\(t,e) -> SExpr [ t, e]) clauses)

pprint :: SExpr -> Doc
pprint (Atom s)       = text s
pprint (IntConst i)   = int i
pprint (SExpr [])     = lparen <> rparen
pprint (SExpr [x])    = parens $ pprint x
pprint (SExpr (Atom "defconst":x:xs)) 
    = parens $ (text "defconst" <+> pprint x)
               $$ nest 1 (vcat (map pprint xs))
pprint (SExpr (Atom "defun":Atom x:SExpr args:body))
    = parens $ (text "defun" <+> text x <+> parens (hsep $ map pprint args))
               $$ nest 1 (vcat (map pprint body))
pprint (SExpr (Atom "let":SExpr l:xs))
    = parens $ (text "let" <+> parens (vcat $ map pprint l))
               $$ nest 1 (vcat (map pprint xs))
pprint (SExpr (x:xs)) = parens $ pprint x <+> sep (map pprint xs)
