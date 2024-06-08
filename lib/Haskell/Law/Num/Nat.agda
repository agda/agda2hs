module Haskell.Law.Num.Nat where

open import Haskell.Prim
open import Haskell.Prim.Num

open import Haskell.Law.Equality
open import Haskell.Law.Num.Def

addNat-suc : ∀ m n → m + suc n ≡ suc (m + n)
addNat-suc zero    n = refl
addNat-suc (suc m) n = cong suc (addNat-suc m n)

addNat-idˡ : ∀ (x : Nat) → 0 + x ≡ x
addNat-idˡ _ = refl

addNat-idʳ : ∀ (x : Nat) → x + 0 ≡ x
addNat-idʳ zero    = refl
addNat-idʳ (suc x) = cong suc (addNat-idʳ x)

addNat-comm : ∀ (x y : Nat) → x + y ≡ y + x
addNat-comm zero    y = sym (addNat-idʳ y)
addNat-comm (suc x) y = begin
  suc (x + y) ≡⟨ cong suc (addNat-comm x y) ⟩
  suc (y + x) ≡⟨ sym (addNat-suc y x) ⟩
  y + suc x   ∎

addNat-assoc : ∀ (x y z : Nat) → (x + y) + z ≡ x + (y + z)
addNat-assoc zero    _ _ = refl
addNat-assoc (suc m) n o = cong suc (addNat-assoc m n o)

mulNat-suc : ∀ (m n : Nat) → m * suc n ≡ m + m * n
mulNat-suc zero    n = refl
mulNat-suc (suc m) n = begin
  suc m * suc n         ≡⟨⟩
  suc n + m * suc n     ≡⟨ cong (suc n +_) (mulNat-suc m n) ⟩
  suc n + (m + m * n)   ≡⟨⟩
  suc (n + (m + m * n)) ≡⟨ cong suc (sym (addNat-assoc n m (m * n))) ⟩
  suc (n + m + m * n)   ≡⟨ cong (λ x → suc (x + m * n)) (addNat-comm n m) ⟩
  suc (m + n + m * n)   ≡⟨ cong suc (addNat-assoc m n (m * n)) ⟩
  suc (m + (n + m * n)) ≡⟨⟩
  suc m + suc m * n     ∎

mulNat-idˡ : ∀ (x : Nat) → 1 * x ≡ x
mulNat-idˡ = addNat-idʳ

mulNat-idʳ : ∀ (x : Nat) → x * 1 ≡ x
mulNat-idʳ zero    = refl
mulNat-idʳ (suc x) = cong suc (mulNat-idʳ x)

mulNat-zeroˡ : ∀ (x : Nat) → 0 * x ≡ 0
mulNat-zeroˡ _ = refl

mulNat-zeroʳ : ∀ (x : Nat) → x * 0 ≡ 0
mulNat-zeroʳ zero    = refl
mulNat-zeroʳ (suc x) = mulNat-zeroʳ x

mulNat-comm : ∀ (x y : Nat) → x * y ≡ y * x
mulNat-comm zero y    = sym (mulNat-zeroʳ y)
mulNat-comm (suc x) y = begin
  suc x * y  ≡⟨⟩
  y + x * y  ≡⟨ cong (y +_) (mulNat-comm x y) ⟩
  y + y * x  ≡⟨ sym (mulNat-suc y x) ⟩
  y * suc x  ∎

mulNat-distributeʳ-addNat : ∀ (x y z : Nat) → (y + z) * x ≡ (y * x) + (z * x)
mulNat-distributeʳ-addNat _ zero    _ = refl
mulNat-distributeʳ-addNat x (suc y) z = begin
  (suc y + z) * x     ≡⟨⟩
  x + (y + z) * x     ≡⟨ cong (x +_) (mulNat-distributeʳ-addNat x y z) ⟩
  x + (y * x + z * x) ≡⟨ sym (addNat-assoc x (y * x) (z * x)) ⟩
  x + y * x + z * x   ≡⟨⟩
  suc y * x + z * x   ∎

mulNat-distributeˡ-addNat : ∀ (x y z : Nat) → x * (y + z) ≡ (x * y) + (x * z)
mulNat-distributeˡ-addNat x y z
  -- This proof transform left distribution to right distribution by using commutativity of *.
  --                                 the initial goal is:  x * (y + z) ≡ (x * y) + (x * z)
  rewrite (mulNat-comm x (y + z)) -- makes or goal become: (y + z) * x ≡ (x * y) + (x * z)
  rewrite (mulNat-comm x y)       -- makes or goal become: (y + z) * x ≡ (y * x) + (x * z)
  rewrite (mulNat-comm x z)       -- makes or goal become: (y + z) * x ≡ (y * x) + (z * x)
  = mulNat-distributeʳ-addNat x y z

mulNat-assoc : ∀ (x y z : Nat) → (x * y) * z ≡ x * (y * z)
mulNat-assoc zero    _ _ = refl
mulNat-assoc (suc x) y z = begin
  (suc x * y) * z     ≡⟨⟩
  (y + x * y) * z     ≡⟨ mulNat-distributeʳ-addNat z y (x * y) ⟩
  y * z + (x * y) * z ≡⟨ cong (y * z +_) (mulNat-assoc x y z) ⟩
  y * z + x * (y * z) ≡⟨⟩
  suc x * (y * z)     ∎

instance
  iLawfulNumNat : IsLawfulNum Nat
  iLawfulNumNat .IsLawfulNum.+-assoc      = addNat-assoc
  iLawfulNumNat .IsLawfulNum.+-comm       = addNat-comm
  iLawfulNumNat .IsLawfulNum.+-idˡ x      = addNat-idˡ x
  iLawfulNumNat .IsLawfulNum.+-idʳ x      = addNat-idʳ x
  iLawfulNumNat .IsLawfulNum.neg-inv zero = refl -- inline this proof because it has not much use anyway I guess?
  iLawfulNumNat .IsLawfulNum.*-assoc      = mulNat-assoc
  iLawfulNumNat .IsLawfulNum.*-idˡ x      = mulNat-idˡ x
  iLawfulNumNat .IsLawfulNum.*-idʳ x      = mulNat-idʳ x
  iLawfulNumNat .IsLawfulNum.distributeˡ  = mulNat-distributeˡ-addNat
  iLawfulNumNat .IsLawfulNum.distributeʳ  = mulNat-distributeʳ-addNat
