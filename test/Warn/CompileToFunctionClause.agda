module CompileToFunctionClause where

open import Haskell.Prelude

-- The target function is an existing definition with a regular COMPILE pragma.
target : Bool → Bool
target True  = True
target False = False
{-# COMPILE AGDA2HS target #-}

-- The source function has the same type as the target, but its clauses are
-- different. Uses of `source` are compiled to `target`, so the generated
-- Haskell code still compiles, but it has different semantics from the Agda
-- source. agda2hs warns instead of reporting an error.
source : Bool → Bool
source True  = False
source False = True
{-# COMPILE AGDA2HS source to target #-}

-- A local helper whose argument shadows a pattern variable of the enclosing
-- function. The helper of `sourceShadow` returns the enclosing parameter,
-- while the helper of `targetShadow` returns its own argument. The two
-- functions are not alpha-equivalent: shadowing must not be ignored.
targetShadow : Nat → Nat
targetShadow x = go 0
  where
    go : Nat → Nat
    go x = x

sourceShadow : Nat → Nat
sourceShadow x = go 0
  where
    go : Nat → Nat
    go y = x

{-# COMPILE AGDA2HS targetShadow #-}
{-# COMPILE AGDA2HS sourceShadow to targetShadow #-}
