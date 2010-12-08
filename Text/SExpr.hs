-- |
-- Module      : Text.SExpr
-- Copyright   : Robert Atkey 2010
-- License     : BSD3
--
-- Maintainer  : bob.atkey@gmail.com
-- Stability   : experimental
-- Portability : unknown
--
-- Simple representation of S-expressions, and pretty printing
-- thereof. Mainly used for generation of Emacs Lisp code.

module Text.SExpr where

import Text.PrettyPrint

data SExpr = Atom     String
           | IntConst Int
           | SExpr    [SExpr]

cond :: [([SExpr], SExpr)] -> SExpr
cond clauses = SExpr (Atom "cond" : map (\(t,e) -> SExpr [ SExpr t, e]) clauses)

pprint :: SExpr -> Doc
pprint (Atom s)       = text s
pprint (IntConst i)   = int i
pprint (SExpr [])     = lparen <> rparen
pprint (SExpr [x])    = parens $ pprint x
pprint (SExpr (x:xs)) = parens $ pprint x <+> sep (map pprint xs)
