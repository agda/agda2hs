
open import Haskell.Prelude

record ∃ (A : Set) (@0 P : A → Set) : Set where
  constructor _[_]
  field
    el : A
    @0 pf : P el
open ∃ public

{-# COMPILE AGDA2HS ∃ unboxed #-}

postulate
  IsSorted : List Int → Set
  looksfine : {xs : List Int} → IsSorted xs

sort1 : List Int → ∃ (List Int) IsSorted
sort1 xs = xs [ looksfine ]

{-# COMPILE AGDA2HS sort1 #-}

sort2 : List Int → ∃ (List Int) IsSorted
sort2 xs .el = xs
sort2 xs .pf = looksfine

{-# COMPILE AGDA2HS sort2 #-}

sort3 : List Int → ∃ (List Int) IsSorted
sort3 xs = xs [ sort2 xs .pf ]

{-# COMPILE AGDA2HS sort3 #-}

sortAll : List (List Int)
sortAll = map el (map (λ xs → xs [ looksfine {xs} ]) ((1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ []))

{-# COMPILE AGDA2HS sortAll #-}

record Σ0 (A : Set) (P : @0 A → Set) : Set where
  constructor _[_]
  field
    @0 el : A
    pf : P el
open Σ0 public

{-# COMPILE AGDA2HS Σ0 unboxed #-}

Scope : (name : Set) → Set
Scope name = Σ0 (List name) λ xs → ∃ Int λ n → length xs ≡ n

{-# COMPILE AGDA2HS Scope #-}

emptyScope : {name : Set} → Scope name
emptyScope = [] [ 0 [ refl ] ]

{-# COMPILE AGDA2HS emptyScope #-}
