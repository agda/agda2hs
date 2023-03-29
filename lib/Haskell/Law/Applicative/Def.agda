module Haskell.Law.Applicative.Def where

open import Haskell.Prim
open import Haskell.Prim.Functor

open import Haskell.Prim.Applicative
open import Haskell.Prim.Monoid
open import Haskell.Prim.Tuple

open import Haskell.Law.Functor

record IsLawfulApplicative (F : Set → Set) ⦃ iAppF : Applicative F ⦄ : Set₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulFunctor F

    -- Identity: pure id <*> v = v
    identity : (v : F a) → (pure id <*> v) ≡ v

    -- Composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
    composition : {a b c : Set} → (u : F (b → c)) (v : F (a → b)) (w : F a)
      → (pure _∘_ <*> u <*> v <*> w) ≡ (u <*> (v <*> w))

    -- Homomorphism: pure f <*> pure x = pure (f x)
    homomorphism : {a b : Set} → (f : a → b) (x : a)
      → (Applicative._<*>_ iAppF (pure f) (pure x)) ≡ (pure (f x))

    -- Interchange: u <*> pure y = pure ($ y) <*> u
    interchange : {a b : Set} → (u : F (a → b)) (y : a)
      → (u <*> (pure y)) ≡ (pure (_$ y) <*> u)

    -- fmap f x = pure f <*> x
    functor : (f : a → b) (x : F a) → (fmap f x) ≡ ((pure f) <*> x)

open IsLawfulApplicative ⦃ ... ⦄ public

instance postulate
  iLawfulApplicativeFun : IsLawfulApplicative (λ b → a → b)

  iLawfulApplicativeTuple₂ : ⦃ Monoid a ⦄ → Applicative (a ×_)

  iLawfulApplicativeTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Applicative (a × b ×_)

  iLawfulApplicativeTuple₄ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ⦃ Monoid c ⦄ →
    Applicative (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))

