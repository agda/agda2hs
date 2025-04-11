module Haskell.Law.Nat where

open import Haskell.Prim
open import Haskell.Prim.Num

open import Haskell.Law.Def
open import Haskell.Law.Equality

suc-injective : Injective suc
suc-injective refl = refl

{-|
The canonical formalization of the
less-than-or-equal-to relation for natural numbers.
-}
data _≤_ : Nat → Nat → Type where
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

x≤x+1 : ∀ (x : Nat) → x ≤ suc x
x≤x+1 zero    = z≤n
x≤x+1 (suc x) = s≤s (x≤x+1 x)

x+[y-x]≡y : ∀ (x y : Nat) → x ≤ y → x + monusNat y x ≡ y
x+[y-x]≡y   zero       y       x≤y  = refl
x+[y-x]≡y (suc x) (suc y) (s≤s x≤y) = cong suc (x+[y-x]≡y x y x≤y)

y-x≤y : ∀ (x y : Nat) → monusNat y x ≤ y
y-x≤y zero         y  = ≤-refl y
y-x≤y (suc x)   zero  = z≤n
y-x≤y (suc x) (suc y) = ≤-trans (y-x≤y x y) (x≤x+1 y)
