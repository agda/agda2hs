module Haskell.Law.Eq.Util where

open import Haskell.Extra.Dec

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq

open import Haskell.Law.Bool
open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality

substEq : {@0 a : Set} → ⦃ @0 iEqA : Eq a ⦄ → ⦃ @0 iLawfulEqA : IsLawfulEq a ⦄ 
        → (@0 p : @0 a → Set) {@0 x y : a} 
        → @0 (x == y) ≡ True → p x 
        → p y
substEq p { x } { y } h z = subst0 p (equality h) z
{-# COMPILE AGDA2HS substEq transparent #-}

congEq : ⦃ iEqA : Eq a ⦄ → ⦃ iLawfulEqA : IsLawfulEq a ⦄ 
       → (p : a → b) {x y : a} 
       → (x == y) ≡ True
       → p x ≡ p y
congEq p { x } { y } h = cong p (equality h)

substEq₂ : {@0 a b : Set} 
        → ⦃ iEqA : Eq a ⦄ → ⦃ iLawfulEqA : IsLawfulEq a ⦄ 
        → ⦃ iEqB : Eq b ⦄ → ⦃ iLawfulEqB : IsLawfulEq b ⦄ 
        → (@0 p : @0 a → @0 b → Set) {@0 x y : a} {@0 t s : b}
        → @0 (x == y) ≡ True → @0 (t == s) ≡ True 
        → p x t 
        → p y s
substEq₂ p { x } { y } { t } { s } hxy hts z = substEq (p y) hts (substEq (λ r → p r t) hxy z)
{-# COMPILE AGDA2HS substEq₂ transparent #-}

congEq₂ : ⦃ iEqA : Eq a ⦄ → ⦃ iLawfulEqA : IsLawfulEq a ⦄ 
        → ⦃ iEqB : Eq b ⦄ → ⦃ iLawfulEqB : IsLawfulEq b ⦄ 
        → (p : a → b → c) {x y : a} {t s : b}
        → (x == y) ≡ True → (t == s) ≡ True 
        → p x t ≡ p y s
congEq₂ p { x } { y } { t } { s } hxy hts = cong₂ p (equality hxy) (equality hts)
