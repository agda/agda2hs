module Haskell.Law.Applicative.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Applicative
open import Haskell.Prim.Functor

open import Haskell.Law.Applicative.Def

open import Haskell.Law.Equality
open import Haskell.Law.List

private
  identityList : {a : Set} → (v : List a) → (pure id <*> v) ≡ v
  identityList [] = refl
  identityList (x ∷ xs)
    rewrite identityList xs
    = refl

  compositionList : {a b c : Set} → (u : List (b → c)) (v : List (a → b)) (w : List a) 
    → ((((pure _∘_) <*> u) <*> v) <*> w) ≡ (u <*> (v <*> w))
  compositionList [] _  _  = refl
  compositionList us vs ws = trustMe -- TODO

  interchangeList : {a b : Set} → (u : List (a → b)) → (y : a) 
    → (u <*> (pure y)) ≡ (pure (_$ y) <*> u)
  interchangeList [] _ = refl
  interchangeList (x ∷ xs) y 
      rewrite interchangeList xs y
      = refl

  functorList : {a b : Set} → (f : a → b) → (x : List a) 
    → (fmap f x) ≡ ((pure f) <*> x)
  functorList _ [] = refl
  functorList f (x ∷ xs)
      rewrite functorList f xs 
        | ++-[] (map f xs)
        | ++-[] (f x ∷ map f xs)
      = refl

instance
  iLawfulApplicativeList : IsLawfulApplicative List
  iLawfulApplicativeList = λ where
    .identity → identityList
    .composition → compositionList
    .homomorphism _ x → refl
    .interchange → interchangeList
    .functor → functorList
