module Haskell.Law.Either where

open import Haskell.Prim
open import Haskell.Prim.Either

Left-injective : ∀ {a b : Set} {z w : a} 
    → (x y : Either a b) → ⦃ x ≡ Left z ⦄ → ⦃ y ≡ Left w ⦄ -> x ≡ y 
    → z ≡ w
Left-injective (Left x) (Left y) ⦃ refl ⦄ ⦃ refl ⦄ refl = refl

Right-injective : ∀ {a b : Set} {z w : b} 
    → (x y : Either a b) → ⦃ x ≡ Right z ⦄ → ⦃ y ≡ Right w ⦄ -> x ≡ y 
    → z ≡ w
Right-injective (Right x) (Right y) ⦃ refl ⦄ ⦃ refl ⦄ refl = refl
