module NatLitPat where

open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Haskell.Prelude

data RecHelp₁ : Nat → Set where
  ≡0 : RecHelp₁ 0
  ≢0 : {n : Nat} → ⦃ _ : Num.MinusOK iNumNat n 1 ⦄ → RecHelp₁ (n - 1) → RecHelp₁ n

data RecHelp₂ : Nat → Set where
  ≡0 : RecHelp₂ 0
  ≡1 : RecHelp₂ 1
  >1 : {n : Nat} → ⦃ _ : Num.MinusOK iNumNat n 1 ⦄ → ⦃ _ : Num.MinusOK iNumNat n 2 ⦄ →
       RecHelp₂ (n - 1) → RecHelp₂ (n - 2) → RecHelp₂ n

instance
  @0 recHelp₁ : {n : Nat} → RecHelp₁ n
  recHelp₁ {zero}  = ≡0
  recHelp₁ {suc n} = ≢0 (recHelp₁ {n})

  @0 recHelp₂ : {n : Nat} → RecHelp₂ n
  recHelp₂ {zero}        = ≡0
  recHelp₂ {suc 0}       = ≡1
  recHelp₂ {suc (suc n)} = >1 (recHelp₂ {suc n}) (recHelp₂ {n})

fac : (n : Nat) → ⦃ @0 _ : RecHelp₁ n ⦄ → Nat
fac 0          = 1
fac n ⦃ ≢0 r ⦄ = n * fac (n - 1) ⦃ r ⦄

{-# COMPILE AGDA2HS fac #-}

fib : (n : Nat) → ⦃ @0 _ : RecHelp₂ n ⦄ → Nat
fib 0              = 0
fib 1              = 1
fib n ⦃ >1 r₁ r₂ ⦄ = fib (n - 1) ⦃ r₁ ⦄ + fib (n - 2) ⦃ r₂ ⦄

{-# COMPILE AGDA2HS fib #-}

proof₁ : fac 5 ≡ 120
proof₁ = refl

proof₂ : fib 10 ≡ 55
proof₂ = refl
