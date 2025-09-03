
open import Haskell.Prelude

{-# NO_POSITIVITY_CHECK #-}
record SUL (sul : Set → Set → Set) : Set₂ where
  field
    step  : ∀ {i o} → sul i o → i → (sul i o × o)
    reset : ∀ {i o} → sul i o → sul i o

{-# COMPILE AGDA2HS SUL class #-}

open SUL {{...}}  -- open fields from instance

-- Automaton class, with `current` method only for now
record Automaton (aut : Set → Set → Set → Set) : Set₃ where
  field
    overlap ⦃ super ⦄ : ∀ {s} → SUL (aut s)
    current : ∀ {s i o} → aut s i o → s

open Automaton {{...}}

{-# COMPILE AGDA2HS Automaton class #-}
