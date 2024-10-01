Release notes for agda2hs v1.3
==============================

Changes
-------

Changes to agda2hs:
- Increased Agda base version to 2.7
- Increased bounds to support GHC 9.8.4 and GHC 9.10.2
- Re-implemented the canonicity check for instances to be simpler but more robust
- Added {-# COMPILE AGDA2HS ... inline #-} pragma for marking definitions to be inlined during compilation to Haskell
- Added {-# COMPILE AGDA2HS ... tuple #-} pragma for compiling record types in Agda to a tuple type in Haskell
- Non-erased implicit arguments and instance arguments are now compiled to regular arguments in Haskell
- Non-erased module parameters are now compiled to regular arguments in Haskell
- Rank-N Haskell types are now supported
- Added `agda2hs locate` command printing the path to the agda2hs prelude `.agda-lib` file

Additions to the agda2hs Prelude:
- New module `Haskell.Extra.Dec` for working with decidability proofs (compiled to `Bool`)
- New module `Haskell.Extra.Refinement` for working with refinement types (compiled to the base type)
- New module `Haskell.Extra.Erase` for working with erased types (compiled to `()`)
- New module `Haskell.Extra.Sigma` for working with dependent pair types (compiled to tuples)
- New module `Haskell.Extra.Loop` providing a safe `loop` function (using an erased fuel argument)
- New module `Haskell.Extra.Delay` providing a `Delay` monad for non-termination (compiled to pure functions in Haskell)
- New function `the` in `Haskell.Prim` for generating Haskell type annotations
- Added properties to `Haskell.Law.Equality`: `subst`, `subst0`
- Added properties to `Haskell.Law.Bool`: `ifFlip`, `ifTrueEqThen`, `ifFalseEqThen`
- Added properties to `Haskell.Law.List`: `map-concatMap`, `map-<*>-recomp`, `concatMap-++-distr`
- Added proofs that many of the instances defined in the prelude are lawful

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.3+is%3Apr for the full list of changes.

Fixed issues
------------

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.3+is%3Aissue for the full list of fixed issues.
