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
