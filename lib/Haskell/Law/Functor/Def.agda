module Haskell.Law.Functor.Def where

open import Haskell.Prim
open import Haskell.Prim.Either
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple

open import Haskell.Prim.Functor

record IsLawfulFunctor (func : Set → Set) ⦃ iFuncF : Functor func ⦄ : Set₁ where
  field
    -- Identity: fmap id == id
    identity : (fa : func a) → (Functor.fmap iFuncF id) fa ≡ id fa

    -- Composition: fmap (f . g) == fmap f . fmap g
    composition : (fa : func a) → (f : a → b) → (g : b → c)
      → (Functor.fmap iFuncF (g ∘ f)) fa ≡ ((Functor.fmap iFuncF g) ∘ (Functor.fmap iFuncF f)) fa
        
open IsLawfulFunctor ⦃ ... ⦄ public
 
instance
  postulate iLawfulFunctorFun : IsLawfulFunctor (λ b → a → b)

  postulate iLawfulFunctorTuple₂ : IsLawfulFunctor (a ×_)

  postulate iLawfulFunctorTuple₃ : IsLawfulFunctor (a × b ×_)

  postulate iLawfulFunctorTuple₄ : IsLawfulFunctor (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))

