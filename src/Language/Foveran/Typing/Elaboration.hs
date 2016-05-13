module Language.Foveran.Typing.Elaborator
    where

-- Given a collection of holes, some of which have elaboration
-- directives in, we “execute” the elaboration directives, using the
-- current context and result type as guides.

-- The minimum collection of elaboration directives includes:
-- - “coercion please”: given a pair of types, unify them
-- - “perform rewrite”: given a goal type, match against it to discover where to do rewrites
-- - “eliminate data”:  generalised data elimination, incorporating elimination with a motive
-- - “eliminate empty”: given a goal type, generate an Empty elimination

elaborate :: DS.TermPos -> Value -> Maybe CS.Term -- with holes, and maybe errors
elaborate term vtype = do
  -- turn the term into a locally nameless term, with holes for the elaboration points
  -- run the type checker
  -- get back a list of holes to fill in


-- Plan for attempting to solve a collection of holes:
-- - Given a collection of holes, the ones with elaboration hints attached are processed
-- - Basic interface to holes:



-- Say that the hole's elaboration hint is “Eliminate tm [clauses]”
-- We synthesise a type for tm, by calling out to the type checker [what to do if more holes are generated?] [is this just recursive elaboration?]
--   - how to cope with speculative checking of terms with holes?
-- Looking at the type of ‘tm’, we check that there are the right clauses
-- Then “fill” the hole with the correct eliminator, with further holes left for the stuff in the clauses

-- The term being eliminated with be type-checked multiple times, due
-- to the first attempt to discover its type, and then again when
-- checking that the whole eliminator is well-typed.

-- could we get the type checker to synthesise some types for us the
-- first time round, and then use that instead of calling the type
-- checker recursively. This will still end up checking the same term
-- twice... and potentially generating the same holes more than once.

-- plan:
-- - type check term
-- - for each hole that has an elaboration hint, call the appropriate elaborator to discover how to elaborate it
-- - this will return a new locally nameless term to be passed to the type checker
-- - this might generate new holes to be solved by the elaborator

-- - the elaborator might need to call out to the type checker to
-- synthesise a type for something. At the moment, we could just
-- refuse to accept the further generation of holes.

-- HoleContexts should work as zippers, so that new holes get inserted
-- into the right place, and hole lookups do the right thing.


-- Plan B:
-- - have an extensible type checker that essentially works like the current one in terms of new syntax.
-- - everything gets elaborated into the core type theory.
-- - instead of generating holes, we are allowed to call out immediately to 

-- For “Eliminate tm [clauses]”:
--   input: the desired goal type, the local context
--   steps:
--     1. synthesise a type for “tm”
--     2. if the type is of the form “µI I (\i -> “Sg” (1 + .. + 1) f) i” then check that we have the right number of clauses
--     3. Work out an appropriate eliminator type from the goal type
--     4. return a term that looks like “inductionI I (\i x. P) (\i x. case fst x for ... with { blah } (snd x)) tm”
--        where blah contains the appropriate stuff to ensure that 

-- This will entail checking “tm” again to make sure it fits in this
-- context. This is probably ok. We should make sure that elaborating
-- “tm” the first time round completely succeeds. At the very least,
-- we cannot allow the holes it generates to be included in the set of
-- holes in the term. I think it is best to just synthesise a type for
-- the term, and if it comes back with extra holes, then raise an
-- error.


-- Hole filling:
-- - given an incomplete term [holes, tm]
-- - focus on a particular hole: (LocalContext, Goal)
-- - give a term to fill it in, which generates some new holes (if the type check succeeds)
-- - substitute the newly filled in hole into all the later holes and the term

-- Would really like to interleave hole-filling by elaboration with
-- type checking, so that we don't end up bouncing back and forth
-- between holes and type-checking.

-- OTOH, the explicit holes thing is much cleaner, conceptually.

