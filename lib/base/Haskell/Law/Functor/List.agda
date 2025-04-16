module Haskell.Law.Functor.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Functor

open import Haskell.Law.Equality
open import Haskell.Law.Functor.Def

private
  identityList : (fa : List a) → (fmap id) fa ≡ id fa
  identityList [] = refl
  identityList (x ∷ xs) rewrite identityList xs = refl

  compositionList : (fa : List a) → (f : a → b) → (g : b → c)
    → fmap (g ∘ f) fa ≡ (fmap g ∘ fmap f) fa
  compositionList [] _ _ = refl
  compositionList (x ∷ xs) f g rewrite compositionList xs f g = refl

instance
  iLawfulFunctorList : IsLawfulFunctor List
  iLawfulFunctorList = λ where
    .identity → identityList
    .composition → compositionList
