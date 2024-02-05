module Haskell.Law.Eq.Either where

open import Haskell.Prim
open import Haskell.Prim.Either
open import Haskell.Prim.Eq

open import Haskell.Extra.Dec

open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality
open import Haskell.Law.Either

isEqualityEither : ⦃ iEqA : Eq a ⦄ → ⦃ iEqB : Eq b ⦄ → ⦃ IsLawfulEq a ⦄ → ⦃ IsLawfulEq b ⦄ 
    → ∀ (x y : Either a b) → Reflects (x ≡ y) (x == y)
isEqualityEither   (Left  x)   (Right y) = λ ()
isEqualityEither   (Right x)   (Left  y) = λ ()
isEqualityEither a@(Left  x) b@(Left  y) = mapReflects 
    (cong Left) 
    (Left-injective a b)  
    (isEquality x y)
isEqualityEither a@(Right x) b@(Right y) = mapReflects 
    (cong Right) 
    (Right-injective a b)  
    (isEquality x y)

instance
  iLawfulEqEither : ⦃ iEqA : Eq a ⦄ → ⦃ iEqB : Eq b ⦄ → ⦃ IsLawfulEq a ⦄ → ⦃ IsLawfulEq b ⦄ 
    → IsLawfulEq (Either a b)
  iLawfulEqEither = λ where       
    .isEquality -> isEqualityEither
