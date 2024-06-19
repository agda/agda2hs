module Haskell.Prim.Function where

open import Haskell.Prim

{-|
Pointwise equality on functions.
This says that two functions produce the same
result for all input values.
-}
infix 4 _≗_
_≗_ : ∀ {A B : Set} (f g : A → B) → Set
f ≗ g = ∀ a → f a ≡ g a

Commutative : {a : Set} → (a → a → a) → Set
Commutative _+_ = ∀ x y → x + y ≡ y + x

Associative : {a : Set} → (a → a → a) → Set
Associative _+_ = ∀ x y z → (x + y) + z ≡ x + (y + z)

Identityˡ : {a : Set} → (a → a → a) → a → Set
Identityˡ _+_ 𝟘 = ∀ x → 𝟘 + x ≡ x

Identityʳ : {a : Set} → (a → a → a) → a → Set
Identityʳ _+_ 𝟘 = ∀ x → x + 𝟘 ≡ x

Distributiveˡ : {a : Set} → (_+_ : a → a → a) → (_*_ : a → a → a) → Set
Distributiveˡ _+_ _*_ = ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)

Distributiveʳ : {a : Set} → (_+_ : a → a → a) → (_*_ : a → a → a) → Set
Distributiveʳ _+_ _*_ =  ∀ x y z → (y + z) * x ≡ (y * x) + (z * x)

{-|
Definition of homomorphism over unary functions.
A function φ is homomorphic w.r.t. some function or structure f
when it preserves this structure in its target domain b
(where this structure is called g).
-}
Homomorphism₁ : ∀ {a b : Set} (f : a → a) (g : b → b)
  → (φ : a → b) → Set
Homomorphism₁ f g φ = φ ∘ f ≗ g ∘ φ

{-|
Definition of homomorphism over binary functions.
A function φ is homomorphic w.r.t. some structure _+ᵃ_
when it preserves this structure in its target domain b
(where this structure is called _+ᵇ_).
-}
Homomorphism₂ : ∀ {a b : Set} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b)
  → (φ : a → b) → Set
Homomorphism₂ _+ᵃ_ _+ᵇ_ φ = ∀ x y → φ (x +ᵃ y) ≡ φ x +ᵇ φ y

record Embedding₂ {a b : Set} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) : Set where
  field
    hom   : Homomorphism₂ _+ᵃ_ _+ᵇ_ φ
    embed : φ⁻¹ ∘ φ ≗ id

record MonoidEmbedding₂ {a b : Set} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) (0ᵃ : a) (0ᵇ : b) : Set where
  field
    embedding : Embedding₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹
    0-hom     : φ 0ᵃ ≡ 0ᵇ

