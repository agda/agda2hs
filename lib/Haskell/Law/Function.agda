module Haskell.Law.Function where

open import Haskell.Prim
open import Haskell.Law.Equality


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

module _ {a b : Set}
  (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b)
  (_*ᵃ_ : a → a → a) (_*ᵇ_ : b → b → b)
  (f : a → b) (g : b → a)
  (embed : g ∘ f ≗ id)
  (+-hom : Homomorphism₂ _+ᵃ_ _+ᵇ_ f)
  (*-hom : Homomorphism₂ _*ᵃ_ _*ᵇ_ f)
  where

  map-distributeˡ : Distributiveˡ _+ᵇ_ _*ᵇ_ → Distributiveˡ _+ᵃ_ _*ᵃ_
  map-distributeˡ distributeˡ-b x y z =
    x *ᵃ (y +ᵃ z)                    ≡˘⟨ embed (x *ᵃ (y +ᵃ z)) ⟩
    g (f (x *ᵃ (y +ᵃ z)))            ≡⟨ cong g (*-hom x (y +ᵃ z)) ⟩
    g (f x *ᵇ f (y +ᵃ z))            ≡⟨ cong g (cong (f x *ᵇ_) (+-hom y z)) ⟩
    g (f x *ᵇ (f y +ᵇ f z))          ≡⟨ cong g (distributeˡ-b (f x) (f y) (f z)) ⟩
    g ((f x *ᵇ f y) +ᵇ (f x *ᵇ f z)) ≡˘⟨ cong g (cong (_+ᵇ (f x *ᵇ f z)) (*-hom x y)) ⟩
    g (f (x *ᵃ y) +ᵇ (f x *ᵇ f z))   ≡˘⟨ cong g (cong (f (x *ᵃ y) +ᵇ_) (*-hom x z)) ⟩
    g (f (x *ᵃ y) +ᵇ f (x *ᵃ z))     ≡˘⟨ cong g (+-hom (x *ᵃ y) (x *ᵃ z)) ⟩
    g (f ((x *ᵃ y) +ᵃ (x *ᵃ z)))     ≡⟨ embed ((x *ᵃ y) +ᵃ (x *ᵃ z)) ⟩
    (x *ᵃ y) +ᵃ (x *ᵃ z)             ∎

  map-distributeʳ : Distributiveʳ _+ᵇ_ _*ᵇ_ → Distributiveʳ _+ᵃ_ _*ᵃ_
  map-distributeʳ distributeʳ-b x y z =
    (y +ᵃ z) *ᵃ x                    ≡˘⟨ embed ((y +ᵃ z) *ᵃ x) ⟩
    g (f ((y +ᵃ z) *ᵃ x))            ≡⟨ cong g (*-hom (y +ᵃ z) x) ⟩
    g (f (y +ᵃ z) *ᵇ f x)            ≡⟨ cong g (cong (_*ᵇ f x) (+-hom y z)) ⟩
    g ((f y +ᵇ f z) *ᵇ f x)          ≡⟨ cong g (distributeʳ-b (f x) (f y) (f z)) ⟩
    g ((f y *ᵇ f x) +ᵇ (f z *ᵇ f x)) ≡˘⟨ cong g (cong (_+ᵇ (f z *ᵇ f x)) (*-hom y x)) ⟩
    g (f (y *ᵃ x) +ᵇ (f z *ᵇ f x))   ≡˘⟨ cong g (cong (f (y *ᵃ x) +ᵇ_) (*-hom z x)) ⟩
    g (f (y *ᵃ x) +ᵇ f (z *ᵃ x))     ≡˘⟨ cong g (+-hom (y *ᵃ x) (z *ᵃ x)) ⟩
    g (f ((y *ᵃ x) +ᵃ (z *ᵃ x)))     ≡⟨ embed ((y *ᵃ x) +ᵃ (z *ᵃ x)) ⟩
    (y *ᵃ x) +ᵃ (z *ᵃ x)             ∎
