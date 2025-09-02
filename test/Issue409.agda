
open import Haskell.Prelude

{-# NO_POSITIVITY_CHECK #-}
record SUL (sul : Set → Set → Set) : Set₂ where
  field
    step  : ∀ {i o} → sul i o → i → (sul i o × o)
    reset : ∀ {i o} → sul i o → sul i o

{-# COMPILE AGDA2HS SUL class #-}

open SUL {{...}}

record Automaton (aut : Set → Set → Set) (s : Set) : Set₂ where
  field
    overlap ⦃ super ⦄ : SUL aut
    current : ∀ {i o} → aut i o → s

{-# COMPILE AGDA2HS Automaton class #-}
