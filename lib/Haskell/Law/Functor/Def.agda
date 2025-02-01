module Haskell.Law.Functor.Def where

open import Haskell.Prim
open import Haskell.Prim.Tuple

open import Haskell.Prim.Functor

record IsLawfulFunctor (F : Type → Type) ⦃ iFuncF : Functor F ⦄ : Type₁ where
  field
    -- Identity: fmap id == id
    identity : (fa : F a) → (fmap id) fa ≡ id fa

    -- Composition: fmap (f . g) == fmap f . fmap g
    composition : (fa : F a) (f : a → b) (g : b → c)
      → fmap (g ∘ f) fa ≡ (fmap g ∘ fmap f) fa

open IsLawfulFunctor ⦃ ... ⦄ public

instance postulate
  iLawfulFunctorFun : IsLawfulFunctor (λ b → a → b)

  iLawfulFunctorTuple₂ : IsLawfulFunctor (a ×_)

  iLawfulFunctorTuple₃ : IsLawfulFunctor (a × b ×_)
