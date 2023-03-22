module Haskell.Law.Functor.Def where

open import Haskell.Prim
open import Haskell.Prim.Tuple

open import Haskell.Prim.Functor

record IsLawfulFunctor (func : Set → Set) ⦃ iFuncF : Functor func ⦄ : Set₁ where
  field
    -- Identity: fmap id == id
    identity : {a : Set} → (fa : func a) → (fmap id) fa ≡ id fa

    -- Composition: fmap (f . g) == fmap f . fmap g
    composition : {a b c : Set} → (fa : func a) → (f : a → b) → (g : b → c)
      → fmap (g ∘ f) fa ≡ (fmap g ∘ fmap f) fa
        
open IsLawfulFunctor ⦃ ... ⦄ public
 
instance
  postulate iLawfulFunctorFun : IsLawfulFunctor (λ b → a → b)

  postulate iLawfulFunctorTuple₂ : IsLawfulFunctor (a ×_)

  postulate iLawfulFunctorTuple₃ : IsLawfulFunctor (a × b ×_)

  postulate iLawfulFunctorTuple₄ : IsLawfulFunctor (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))

