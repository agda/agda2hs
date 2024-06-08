module Haskell.Law.Num.Def where

open import Haskell.Prim
open import Haskell.Prim.Num
open import Haskell.Prim.Integer

record IsLawfulNum (a : Set) ⦃ iNum : Num a ⦄ : Set₁ where
  field
    +-assoc : ∀ (x y z : a) → (x + y) + z ≡ x + (y + z)

    +-comm : ∀ (x y : a) → x + y ≡ y + x

    +-idˡ : ∀ (x : a) {{@0 _ : Num.FromIntegerOK iNum 0}}
      → fromInteger 0 + x ≡ x
    +-idʳ : ∀ (x : a) {{@0 _ : Num.FromIntegerOK iNum 0}}
      → x + fromInteger 0 ≡ x

    neg-inv : ∀ (x : a) {{@0 _ : Num.FromIntegerOK iNum 0}} {{@0 _ : Num.NegateOK iNum x}}
      → x + negate x ≡ fromInteger 0

    *-assoc : ∀ (x y z : a) → (x * y) * z ≡ x * (y * z)

    *-idˡ : ∀ (x : a) {{@0 _ : Num.FromIntegerOK iNum 1}}
      → fromInteger 1 * x ≡ x
    *-idʳ : ∀ (x : a) {{@0 _ : Num.FromIntegerOK iNum 1}}
      → x * fromInteger 1 ≡ x

    distributeˡ : ∀ (x y z : a) → x * (y + z) ≡ (x * y) + (x * z)
    distributeʳ : ∀ (x y z : a) → (y + z) * x ≡ (y * x) + (z * x)

    -- We are currently missing the following because toInteger is missing in our Prelude.
    -- "if the type also implements Integral, then fromInteger is a left inverse for toInteger, i.e. fromInteger (toInteger i) == i"
open IsLawfulNum ⦃ ... ⦄ public
