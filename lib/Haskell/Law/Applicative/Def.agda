module Haskell.Law.Applicative.Def where

open import Haskell.Prim
open import Haskell.Prim.Either
open import Haskell.Prim.Foldable
open import Haskell.Prim.Functor
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monoid
open import Haskell.Prim.Tuple

open import Haskell.Prim.Applicative
open import Haskell.Prim.Monoid
    
record IsLawfulApplicative (func : Set → Set) ⦃ iAppF : Applicative func ⦄ : Set₁ where
  field
    -- Identity: pure id <*> v = v
    identity : (v : func a) → (pure id <*> v) ≡ v

    -- Composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
    composition : (u : func (b → c)) (v : func (a → b)) (w : func a) 
      → (Applicative._<*>_ iAppF (Applicative._<*>_ iAppF (Applicative._<*>_ iAppF (Applicative.pure iAppF _∘_) u) v) w) 
        ≡ (Applicative._<*>_ iAppF u (Applicative._<*>_ iAppF v w))

    -- Homomorphism: pure f <*> pure x = pure (f x)
    homomorphism : (f : a → b) → (x : a) 
      → (Applicative._<*>_ iAppF (Applicative.pure iAppF f) (Applicative.pure iAppF x)) ≡ (Applicative.pure iAppF (f x))

    -- Interchange: u <*> pure y = pure ($ y) <*> u
    interchange : (u : func (a → b)) → (y : a) 
      → (Applicative._<*>_ iAppF u (pure y)) ≡ (pure (_$ y) <*> u)

    -- fmap f x = pure f <*> x
    functor : (f : a → b) → (x : func a) 
      → (fmap f x) ≡ ((pure f) <*> x)
  
open IsLawfulApplicative ⦃ ... ⦄ public

instance
  postulate iLawfulApplicativeFun : IsLawfulApplicative (λ b → a → b)
     