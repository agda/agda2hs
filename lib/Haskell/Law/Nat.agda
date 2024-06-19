module Haskell.Law.Nat where

open import Haskell.Prim

open import Haskell.Law.Def
open import Haskell.Law.Equality

suc-injective : Injective suc
suc-injective refl = refl

{-|
The canonical formalization of the
less-than-or-equal-to relation for natural numbers.
-}
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

≤-refl : ∀ (x : Nat) → x ≤ x
≤-refl zero    = z≤n
≤-refl (suc x) = s≤s (≤-refl x)

≤-antisym : ∀ {x y : Nat}
  → x ≤ y
  → y ≤ x
    -----
  → x ≡ y
≤-antisym z≤n       z≤n       = refl
≤-antisym (s≤s x≤y) (s≤s y≤x) = cong suc (≤-antisym x≤y y≤x)

≤-trans : ∀ {x y z : Nat}
  → x ≤ y
  → y ≤ z
    -----
  → x ≤ z
≤-trans z≤n y≤z = z≤n
≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)
