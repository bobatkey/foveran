module Language.Foveran.Typing.Program
    where

-- What happens:
-- - We are given a pair of terms, “ty” that is meant to represent a type, and “tm” that is meant to represent a term
-- - We check that “ty” really is a type, and that there are no left over holes
-- - We check that “tm” is a value of type “tm”. If this generates no holes, then we are finished and we generate a 'Finished' state
-- - If there are generated holes, then we generate an InProgress state, with 

-- “LocalContext” is a list of name bindings and types, used when
-- checking a term.

-- Each hole's type is well-typed in the context of the prior holes,
-- and the program before the ProgramPart in which the hole lives.

-- When filling in a hole, then (a) we may generate further holes,
-- which are spliced into the hole list in the same position as the
-- hole they replaced; (b) we may have to update the goals of
-- dependent holes; and (c) we have to update the final term with the
-- newly term (can this be done lazily?)

-- The typechecker can do one of two things:
-- - check that something is a type
-- - check that something is a term of a given type

-- in either case, it takes a global context to take definitions from,
-- and a hole context to lookup holes in, and may generate further
-- holes. New holes are tacked on the end of the hole context.

data ProgramPart
    = Finished   { partIdentifier :: Ident
                 , partType       :: Value
                 , finishedValue  :: Maybe (CS.Term, Value)
                 }
    | InProgress { partIdentifier  :: Ident
                 , partType        :: Value
                 , inProgressHoles :: HoleContext
                 , inProgressTerm  :: CS.Term
                 }

{------------------------------------------------------------------------------}
newtype Program
    = Program { programParts :: [ProgramPart] }

instance DefinitionContext Program where
    lookupDefinition identifier program = findIn (programParts program)
        where
          findIn [] = Nothing
          findIn (Finished partIdentifier partType finishedValue:parts)
              | partIdentifier == identifier = Just (partType, snd <$> finishedValue)
              | otherwise                    = findIn parts
          findIn (InProgress partIdentifier partType _ _:parts)
              | partIdentifier == identifier = Just (partType, Nothing)
              | otherwise                    = findIn parts

instance UsesIdentifiers Program where
    usedIdentifiers =
        S.fromList . map partIdentifier . programParts

{------------------------------------------------------------------------------}
-- Adding a definition:
addDefinition :: Ident
              -> LN.TermPos
              -> Maybe LN.TermPos
              -> ProgramState
              -> Either (p, HoleContext, LocalContext, TypeError) ProgramState
addDefinition identifier lnType lnTerm program = do
  when (identifier `S.member` usedIdentifiers program) $
       do error "repeated identifier" -- FIXME: proper error
  -- check that the identifier has not yet been used in the program state
  -- check that the purported type really is a type in the current program, and that there are no holes
  -- check that the purported term really has the type.
  -- If holes are generated, then generate ‘InProgress vtyp holes tm’
  -- If no holes are generated, then evaluate the term and generate ‘Finished vtyp (Just (tm, vtm))’

{------------------------------------------------------------------------------}
-- Turn a list of declarations (produced by parsing) into a Program
fromDeclarations :: [DS.Declaration] -> Program
fromDeclarations declarations = undefined
   -- run the type checker on each one, generating a ProgramPart for each one
   -- collect them all into a list

{------------------------------------------------------------------------------}

{-
data FocusedProgramState 
    = FocusedProgramState
      { focusedBefore :: [ProgramPart]
      , focusedOn     :: ProgramPart
      , focusedAfter  :: [ProgramPart]
      }
-}

-- Filling in a hole (partId.holeId):
-- 1. focus on the relevant ProgramPart
-- 2. focus on the relevant Hole, if it exists
-- 3. check the new term
-- 4. If error, then report error
-- 5. If new holes are generated, then splice them in above the hole
-- 6. Substitute the new term into the goals below the hole, and into the final term
-- 7. If the number of holes has fallen to 0, then mark the ProgramPart as finished
-- 8. Otherwise, package up the new hole context and unfinished term

-- Turning a hole into a definition:
-- - 