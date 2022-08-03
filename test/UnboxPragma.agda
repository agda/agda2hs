
open import Haskell.Prelude

record ∃ (A : Set) (P : A → Set) : Set where
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
