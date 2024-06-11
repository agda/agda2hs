module Haskell.Law.Function where

open import Haskell.Prim.Function
open import Haskell.Law.Equality

map-comm : ∀ {a b : Set} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a)
  → Embedding₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹
  → Commutative _+ᵇ_
  → Commutative _+ᵃ_
map-comm _+ᵃ_ _+ᵇ_ φ φ⁻¹ proj comm x y =
  begin
    x +ᵃ y
  ≡˘⟨ embed (x +ᵃ y) ⟩
    φ⁻¹ (φ (x +ᵃ y))
  ≡⟨ cong φ⁻¹ (hom x y) ⟩
    φ⁻¹ (φ x +ᵇ φ y)
  ≡⟨ cong φ⁻¹ (comm (φ x) (φ y)) ⟩
    φ⁻¹ (φ y +ᵇ φ x)
  ≡˘⟨ cong φ⁻¹ (hom y x) ⟩
    φ⁻¹ (φ (y +ᵃ x))
  ≡⟨ embed (y +ᵃ x) ⟩
    y +ᵃ x
  ∎
  where
    open Embedding₂ proj

map-assoc : ∀ {a b : Set} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a)
  → Embedding₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹
  → Associative _+ᵇ_
  → Associative _+ᵃ_
map-assoc _+ᵃ_ _+ᵇ_ φ φ⁻¹ proj assoc x y z =
  begin
    (x +ᵃ y) +ᵃ z
  ≡⟨ sym (embed ((x +ᵃ y) +ᵃ z)) ⟩
    φ⁻¹ (φ ((x +ᵃ y) +ᵃ z))
  ≡⟨ cong φ⁻¹ (hom (x +ᵃ y) z) ⟩
    φ⁻¹ (φ (x +ᵃ y) +ᵇ φ z)
  ≡⟨ cong φ⁻¹ (cong (_+ᵇ φ z) (hom x y)) ⟩
    φ⁻¹ ((φ x +ᵇ φ y) +ᵇ φ z)
  ≡⟨ cong φ⁻¹ (assoc (φ x) (φ y) (φ z)) ⟩
    φ⁻¹ (φ x +ᵇ (φ y +ᵇ φ z))
  ≡⟨ cong φ⁻¹ (cong (φ x +ᵇ_) (sym (hom y z))) ⟩
    φ⁻¹ (φ x +ᵇ φ (y +ᵃ z))
  ≡⟨ cong φ⁻¹ (sym (hom x (y +ᵃ z))) ⟩
    φ⁻¹ (φ (x +ᵃ (y +ᵃ z)))
  ≡⟨ embed (x +ᵃ (y +ᵃ z)) ⟩
    x +ᵃ (y +ᵃ z)
  ∎
  where
    open Embedding₂ proj

map-idˡ : ∀ {a b : Set} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) (0ᵃ : a) (0ᵇ : b)
  → MonoidEmbedding₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹ 0ᵃ 0ᵇ
  → Identityˡ _+ᵇ_ 0ᵇ
  → Identityˡ _+ᵃ_ 0ᵃ
map-idˡ _+ᵃ_ _+ᵇ_ f g 0ᵃ 0ᵇ membed idˡ x =
  0ᵃ +ᵃ x         ≡⟨ sym (embed (0ᵃ +ᵃ x)) ⟩
  g (f (0ᵃ +ᵃ x)) ≡⟨ cong g (hom 0ᵃ x) ⟩
  g (f 0ᵃ +ᵇ f x) ≡⟨ cong g (cong (_+ᵇ f x) 0-hom) ⟩
  g (0ᵇ +ᵇ f x)   ≡⟨ cong g (idˡ (f x)) ⟩
  g (f x)        ≡⟨ embed x ⟩
  x              ∎
  where
    open MonoidEmbedding₂ membed
    open Embedding₂ embedding

map-idʳ : ∀ {a b : Set} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) (0ᵃ : a) (0ᵇ : b)
  → MonoidEmbedding₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹ 0ᵃ 0ᵇ
  → Identityʳ _+ᵇ_ 0ᵇ
  → Identityʳ _+ᵃ_ 0ᵃ
map-idʳ _+ᵃ_ _+ᵇ_ f g 0ᵃ 0ᵇ membed idʳ x =
  x +ᵃ 0ᵃ         ≡⟨ sym (embed (x +ᵃ 0ᵃ)) ⟩
  g (f (x +ᵃ 0ᵃ)) ≡⟨ cong g (hom x 0ᵃ) ⟩
  g (f x +ᵇ f 0ᵃ) ≡⟨ cong g (cong (f x +ᵇ_) 0-hom) ⟩
  g (f x +ᵇ 0ᵇ)   ≡⟨ cong g (idʳ (f x)) ⟩
  g (f x)        ≡⟨ embed x ⟩
  x              ∎
  where
    open MonoidEmbedding₂ membed
    open Embedding₂ embedding
