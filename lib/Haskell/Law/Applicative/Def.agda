module Haskell.Law.Applicative.Def where

open import Haskell.Prim
open import Haskell.Prim.Functor

open import Haskell.Prim.Applicative
open import Haskell.Prim.Monoid

open import Haskell.Law.Functor

record IsLawfulApplicative (func : Set → Set) ⦃ iAppF : Applicative func ⦄ : Set₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulFunctor func

    -- Identity: pure id <*> v = v
    identity : (v : func a) → (pure id <*> v) ≡ v

    -- Composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
    composition : {a b c : Set} → (u : func (b → c)) (v : func (a → b)) (w : func a)
      → ((((pure _∘_) <*> u) <*> v) <*> w) ≡ (u <*> (v <*> w))

    -- Homomorphism: pure f <*> pure x = pure (f x)
    homomorphism : {a b : Set} → (f : a → b) → (x : a)
      → (Applicative._<*>_ iAppF (pure f) (pure x)) ≡ (pure (f x))

    -- Interchange: u <*> pure y = pure ($ y) <*> u
    interchange : {a b : Set} → (u : func (a → b)) → (y : a)
      → (u <*> (pure y)) ≡ (pure (_$ y) <*> u)

    -- fmap f x = pure f <*> x
    functor : (f : a → b) → (x : func a) → (fmap f x) ≡ ((pure f) <*> x)

open IsLawfulApplicative ⦃ ... ⦄ public

instance
  postulate iLawfulApplicativeFun : IsLawfulApplicative (λ b → a → b)

