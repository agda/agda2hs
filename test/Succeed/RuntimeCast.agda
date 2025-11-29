{-# OPTIONS --erasure #-}

open import Haskell.Prelude
open import Haskell.Control.Exception
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
open import Haskell.Law.Ord

variable
  A A' B B' C C' : Set
  P P' Q Q' : A → Set

it : {{A}} → A
it {{x}} = x

data _~_ : (A : Set) (B : Set) → Set₁
cast  : A ~ B → A → B
cast' : A ~ B → B → A

data _~_ where
  refl : A ~ A

  assert-pre-left : ∀ {A : Set} {B : @0 A → Set}
    → {{Dec A}}
    → ({{@0 x : A}} → B x ~ B')
    → ({{@0 x : A}} → B x) ~ B'

  assert-pre-right : ∀ {A : Set} {B' : @0 A → Set}
    → {{Dec A}}
    → ({{@0 x : A}} → B ~ B' x)
    → B ~ ({{@0 x : A}} → B' x)

  assert-post-left : ∀ {A : Set} {@0 B : A → Set}
    → {{∀ {x} → Dec (B x)}}
    → A ~ A'
    → ∃ A B ~ A'

  assert-post-right : ∀ {A : Set} {@0 B' : A' → Set}
    → {{∀ {x'} → Dec (B' x')}}
    → A ~ A'
    → A ~ ∃ A' B'

  cong-pi : {B : @0 A → Set} {B' : @0 A' → Set}
    → (eA : A ~ A') → (eB : (x : A) (x' : A') → B x ~ B' x')
    → ((x : A) → B x) ~ ((x : A') → B' x)

cast refl x = x
cast (assert-pre-left {A = A} eB) x = assert A (cast eB x)
cast (assert-pre-right eB) x = cast eB x
cast (assert-post-left eA) (x ⟨ _ ⟩) = cast eA x
cast (assert-post-right {B' = B'} eA) x = assert (B' x') (x' ⟨⟩)
  where x' = cast eA x
cast (cong-pi {A = A} eA eB) f x' = cast (eB x x') (f x)
  where x = cast' eA x'

cast' refl x' = x'
cast' (assert-pre-left eB) x' = cast' eB x'
cast' (assert-pre-right {A = A} eB) x' = assert A (cast' eB x')
cast' (assert-post-left {B = B} eA) x' = assert (B x) (x ⟨⟩)
  where x = cast' eA x'
cast' (assert-post-right eA) (x' ⟨ _ ⟩) = cast' eA x'
cast' (cong-pi eA eB) f x = cast' (eB x x') (f x')
  where x' = cast eA x

{-# COMPILE AGDA2HS cast  inline #-}
{-# COMPILE AGDA2HS cast' inline #-}

module Sqrt where

  postulate
    mySqrt : (x : Double) → @0 {{IsTrue (x >= 0)}} → Double

  {-# COMPILE AGDA2HS mySqrt #-}

  eqr : ((x : Double) → @0 {{IsTrue (x >= 0)}} → Double) ~
        ((x : Double) → ∃ Double (λ v → IsTrue (v >= 0) × IsTrue ((abs (x - v * v) <= 0.01))))
  eqr = cong-pi refl (λ x x' → assert-pre-left (assert-post-right refl))

  {-# COMPILE AGDA2HS eqr inline #-}

  checkedSqrt : (x : Double) → ∃ Double (λ y → IsTrue (y >= 0) × IsTrue (abs (x - y * y) <= 0.01))
  checkedSqrt = cast eqr mySqrt

  {-# COMPILE AGDA2HS checkedSqrt #-}

