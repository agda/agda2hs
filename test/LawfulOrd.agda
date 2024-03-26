open import Haskell.Prelude
open import Haskell.Law

data Ordered (a : Set) : Set where
    Gt : ⦃ @0 iOrd : Ord a ⦄ → (a' : a) → (a'' : a) → ⦃ @0 pf : (a' > a'') ≡ True ⦄ → Ordered a
    Lt : ⦃ @0 iOrd : Ord a ⦄ → (a' : a) → (a'' : a) → ⦃ @0 pf : (a' < a'') ≡ True ⦄ → Ordered a
    E :  ⦃ @0 iOrd : Ord a ⦄ → (a' : a) → (a'' : a) → ⦃ @0 pf : a' ≡ a'' ⦄         → Ordered a

{-# COMPILE AGDA2HS Ordered #-}

nLtEq2Gt : ⦃ iOrdA : Ord a ⦄ → ⦃ IsLawfulOrd a ⦄
  → ∀ (x y : a) → ⦃ (x < y) ≡ False ⦄ → ⦃ (x == y) ≡ False ⦄ → (x > y) ≡ True
nLtEq2Gt x y ⦃ h1 ⦄ ⦃ h2 ⦄ =
  begin
    (x > y)
  ≡⟨ sym (not-involution (lte2ngt x y)) ⟩
    not (x <= y)
  ≡⟨ cong not (lte2LtEq x y) ⟩
    not ((x < y) || (x == y))
  ≡⟨ cong (λ b → not (b || (x == y))) h1 ⟩
    not (False || (x == y))
  ≡⟨ cong (λ b → not (False || b)) h2 ⟩
    not (False || False)
  ≡⟨⟩
    True
  ∎

order : ⦃ iOrd : Ord a ⦄ → @0 ⦃ IsLawfulOrd a ⦄
  → (a' : a) → (a'' : a) → Ordered a
order left right =
  if left < right then
    Lt left right
  else (
    if left == right then
      (λ ⦃ h ⦄ → E left right ⦃ equality h ⦄)
    else
      Gt left right ⦃ nLtEq2Gt left right ⦄
  )

{-# COMPILE AGDA2HS order #-}
