module Haskell.Law.Functor.FromMonad where

open import Haskell.Prim

open import Haskell.Prim.Functor
open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def as Monad
open import Haskell.Law.Equality
open import Haskell.Law.Functor

-------------------------------------------------------------------------------
-- Prove the Functor laws from the Monad laws

--
prop-PreLawfulMonad→IsLawfulFunctor
  : ∀ ⦃ _ : Monad m ⦄ ⦃ _ : PreLawfulMonad m ⦄
  → IsLawfulFunctor m
--
prop-PreLawfulMonad→IsLawfulFunctor .identity fa
  rewrite Monad.def-fmap->>= id fa
  = Monad.rightIdentity fa
prop-PreLawfulMonad→IsLawfulFunctor .composition fa f g
  rewrite Monad.def-fmap->>= g (fmap f fa)
  | Monad.def-fmap->>= f fa
  | Monad.def-fmap->>= (g ∘ f) fa
  = begin
    fa >>= (return ∘ g ∘ f)
  ≡⟨ cong-monad fa (λ x → sym (Monad.leftIdentity (f x) _)) ⟩
    fa >>= (λ x → return (f x) >>= (return ∘ g))
  ≡⟨ Monad.associativity _ _ _ ⟩
    (fa >>= (return ∘ f)) >>= (return ∘ g)
  ∎
