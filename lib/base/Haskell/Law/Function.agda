module Haskell.Law.Function where

open import Haskell.Prim
open import Haskell.Law.Equality


{-|
Pointwise equality on functions.
This says that two functions produce the same
result for all input values.
-}
infix 4 _≗_
_≗_ : ∀ {A B : Type} (f g : A → B) → Type
f ≗ g = ∀ a → f a ≡ g a

Commutative : {a : Type} → (a → a → a) → Type
Commutative _+_ = ∀ x y → x + y ≡ y + x

Associative : {a : Type} → (a → a → a) → Type
Associative _+_ = ∀ x y z → (x + y) + z ≡ x + (y + z)

Identityˡ : {a : Type} → (a → a → a) → a → Type
Identityˡ _+_ 𝟘 = ∀ x → 𝟘 + x ≡ x

Identityʳ : {a : Type} → (a → a → a) → a → Type
Identityʳ _+_ 𝟘 = ∀ x → x + 𝟘 ≡ x

Distributiveˡ : {a : Type} → (_+_ : a → a → a) → (_*_ : a → a → a) → Type
Distributiveˡ _+_ _*_ = ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)

Distributiveʳ : {a : Type} → (_+_ : a → a → a) → (_*_ : a → a → a) → Type
Distributiveʳ _+_ _*_ =  ∀ x y z → (y + z) * x ≡ (y * x) + (z * x)

{-|
Definition of homomorphism over unary functions.
A function φ is homomorphic w.r.t. some function or structure f
when it preserves this structure in its target domain b
(where this structure is called g).
-}
Homomorphism₁ : ∀ {a b : Type} (f : a → a) (g : b → b)
  → (φ : a → b) → Type
Homomorphism₁ f g φ = φ ∘ f ≗ g ∘ φ

{-|
Definition of homomorphism over binary functions.
A function φ is homomorphic w.r.t. some structure _+ᵃ_
when it preserves this structure in its target domain b
(where this structure is called _+ᵇ_).
-}
Homomorphism₂ : ∀ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b)
  → (φ : a → b) → Type
Homomorphism₂ _+ᵃ_ _+ᵇ_ φ = ∀ x y → φ (x +ᵃ y) ≡ φ x +ᵇ φ y

record Embedding₂ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) : Type where
  field
    hom   : Homomorphism₂ _+ᵃ_ _+ᵇ_ φ
    embed : φ⁻¹ ∘ φ ≗ id

record MonoidEmbedding₂ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) (0ᵃ : a) (0ᵇ : b) : Type where
  field
    embedding : Embedding₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹
    0-hom     : φ 0ᵃ ≡ 0ᵇ

map-comm : ∀ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a)
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

map-assoc : ∀ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a)
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

map-idˡ : ∀ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) (0ᵃ : a) (0ᵇ : b)
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

map-idʳ : ∀ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) (0ᵃ : a) (0ᵇ : b)
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

module _ {a b : Type}
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

{-|
Dual to `Embedding₂`: a `Surjection₂` pairs a homomorphism `φ` with a map
`φ⁻¹` that is a section of `φ`, i.e. `φ (φ⁻¹ x) ≡ x`. So every element of `b`
is the image of an element of `a`. This lets us transfer laws from the source
type `a` to the target type `b`, which is how the laws for `Word` are obtained
from the laws for `Nat`.
-}
record Surjection₂ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) : Type where
  field
    hom     : Homomorphism₂ _+ᵃ_ _+ᵇ_ φ
    section : φ ∘ φ⁻¹ ≗ id

record MonoidSurjection₂ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) (0ᵃ : a) (0ᵇ : b) : Type where
  field
    surjection : Surjection₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹
    0-hom      : φ 0ᵃ ≡ 0ᵇ

map-comm-surj : ∀ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a)
  → Surjection₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹
  → Commutative _+ᵃ_
  → Commutative _+ᵇ_
map-comm-surj _+ᵃ_ _+ᵇ_ φ φ⁻¹ proj comm x y =
  begin
    x +ᵇ y
  ≡˘⟨ cong (λ z → z +ᵇ y) (section x) ⟩
    φ (φ⁻¹ x) +ᵇ y
  ≡˘⟨ cong (φ (φ⁻¹ x) +ᵇ_) (section y) ⟩
    φ (φ⁻¹ x) +ᵇ φ (φ⁻¹ y)
  ≡˘⟨ hom (φ⁻¹ x) (φ⁻¹ y) ⟩
    φ (φ⁻¹ x +ᵃ φ⁻¹ y)
  ≡⟨ cong φ (comm (φ⁻¹ x) (φ⁻¹ y)) ⟩
    φ (φ⁻¹ y +ᵃ φ⁻¹ x)
  ≡⟨ hom (φ⁻¹ y) (φ⁻¹ x) ⟩
    φ (φ⁻¹ y) +ᵇ φ (φ⁻¹ x)
  ≡⟨ cong (_+ᵇ φ (φ⁻¹ x)) (section y) ⟩
    y +ᵇ φ (φ⁻¹ x)
  ≡⟨ cong (y +ᵇ_) (section x) ⟩
    y +ᵇ x
  ∎
  where
    open Surjection₂ proj

map-assoc-surj : ∀ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a)
  → Surjection₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹
  → Associative _+ᵃ_
  → Associative _+ᵇ_
map-assoc-surj _+ᵃ_ _+ᵇ_ φ φ⁻¹ proj assoc x y z =
  begin
    (x +ᵇ y) +ᵇ z
  ≡˘⟨ cong (λ w → (w +ᵇ y) +ᵇ z) (section x) ⟩
    (φ (φ⁻¹ x) +ᵇ y) +ᵇ z
  ≡˘⟨ cong (λ w → (φ (φ⁻¹ x) +ᵇ w) +ᵇ z) (section y) ⟩
    (φ (φ⁻¹ x) +ᵇ φ (φ⁻¹ y)) +ᵇ z
  ≡˘⟨ cong (λ w → (φ (φ⁻¹ x) +ᵇ φ (φ⁻¹ y)) +ᵇ w) (section z) ⟩
    (φ (φ⁻¹ x) +ᵇ φ (φ⁻¹ y)) +ᵇ φ (φ⁻¹ z)
  ≡˘⟨ cong (_+ᵇ φ (φ⁻¹ z)) (hom (φ⁻¹ x) (φ⁻¹ y)) ⟩
    φ (φ⁻¹ x +ᵃ φ⁻¹ y) +ᵇ φ (φ⁻¹ z)
  ≡˘⟨ hom (φ⁻¹ x +ᵃ φ⁻¹ y) (φ⁻¹ z) ⟩
    φ ((φ⁻¹ x +ᵃ φ⁻¹ y) +ᵃ φ⁻¹ z)
  ≡⟨ cong φ (assoc (φ⁻¹ x) (φ⁻¹ y) (φ⁻¹ z)) ⟩
    φ (φ⁻¹ x +ᵃ (φ⁻¹ y +ᵃ φ⁻¹ z))
  ≡⟨ hom (φ⁻¹ x) (φ⁻¹ y +ᵃ φ⁻¹ z) ⟩
    φ (φ⁻¹ x) +ᵇ φ (φ⁻¹ y +ᵃ φ⁻¹ z)
  ≡⟨ cong (φ (φ⁻¹ x) +ᵇ_) (hom (φ⁻¹ y) (φ⁻¹ z)) ⟩
    φ (φ⁻¹ x) +ᵇ (φ (φ⁻¹ y) +ᵇ φ (φ⁻¹ z))
  ≡⟨ cong (λ w → w +ᵇ (φ (φ⁻¹ y) +ᵇ φ (φ⁻¹ z))) (section x) ⟩
    x +ᵇ (φ (φ⁻¹ y) +ᵇ φ (φ⁻¹ z))
  ≡⟨ cong (x +ᵇ_) (cong (λ w → w +ᵇ φ (φ⁻¹ z)) (section y)) ⟩
    x +ᵇ (y +ᵇ φ (φ⁻¹ z))
  ≡⟨ cong (x +ᵇ_) (cong (y +ᵇ_) (section z)) ⟩
    x +ᵇ (y +ᵇ z)
  ∎
  where
    open Surjection₂ proj

map-idˡ-surj : ∀ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) (0ᵃ : a) (0ᵇ : b)
  → MonoidSurjection₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹ 0ᵃ 0ᵇ
  → Identityˡ _+ᵃ_ 0ᵃ
  → Identityˡ _+ᵇ_ 0ᵇ
map-idˡ-surj _+ᵃ_ _+ᵇ_ φ φ⁻¹ 0ᵃ 0ᵇ membed idˡ x =
  begin
    0ᵇ +ᵇ x
  ≡˘⟨ cong (λ w → w +ᵇ x) 0-hom ⟩
    φ 0ᵃ +ᵇ x
  ≡˘⟨ cong (φ 0ᵃ +ᵇ_) (section x) ⟩
    φ 0ᵃ +ᵇ φ (φ⁻¹ x)
  ≡˘⟨ hom 0ᵃ (φ⁻¹ x) ⟩
    φ (0ᵃ +ᵃ φ⁻¹ x)
  ≡⟨ cong φ (idˡ (φ⁻¹ x)) ⟩
    φ (φ⁻¹ x)
  ≡⟨ section x ⟩
    x
  ∎
  where
    open MonoidSurjection₂ membed
    open Surjection₂ surjection

map-idʳ-surj : ∀ {a b : Type} (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b) (φ : a → b) (φ⁻¹ : b → a) (0ᵃ : a) (0ᵇ : b)
  → MonoidSurjection₂ _+ᵃ_ _+ᵇ_ φ φ⁻¹ 0ᵃ 0ᵇ
  → Identityʳ _+ᵃ_ 0ᵃ
  → Identityʳ _+ᵇ_ 0ᵇ
map-idʳ-surj _+ᵃ_ _+ᵇ_ φ φ⁻¹ 0ᵃ 0ᵇ membed idʳ x =
  begin
    x +ᵇ 0ᵇ
  ≡˘⟨ cong (x +ᵇ_) 0-hom ⟩
    x +ᵇ φ 0ᵃ
  ≡˘⟨ cong (_+ᵇ φ 0ᵃ) (section x) ⟩
    φ (φ⁻¹ x) +ᵇ φ 0ᵃ
  ≡˘⟨ hom (φ⁻¹ x) 0ᵃ ⟩
    φ (φ⁻¹ x +ᵃ 0ᵃ)
  ≡⟨ cong φ (idʳ (φ⁻¹ x)) ⟩
    φ (φ⁻¹ x)
  ≡⟨ section x ⟩
    x
  ∎
  where
    open MonoidSurjection₂ membed
    open Surjection₂ surjection

module _ {a b : Type}
  (_+ᵃ_ : a → a → a) (_+ᵇ_ : b → b → b)
  (_*ᵃ_ : a → a → a) (_*ᵇ_ : b → b → b)
  (f : a → b) (g : b → a)
  (section : f ∘ g ≗ id)
  (+-hom : Homomorphism₂ _+ᵃ_ _+ᵇ_ f)
  (*-hom : Homomorphism₂ _*ᵃ_ _*ᵇ_ f)
  where

  map-distributeˡ-surj : Distributiveˡ _+ᵃ_ _*ᵃ_ → Distributiveˡ _+ᵇ_ _*ᵇ_
  map-distributeˡ-surj distributeˡ-a x y z =
    x *ᵇ (y +ᵇ z)                     ≡˘⟨ cong (λ w → w *ᵇ (y +ᵇ z)) (section x) ⟩
    f (g x) *ᵇ (y +ᵇ z)               ≡˘⟨ cong (f (g x) *ᵇ_) (cong (λ w → w +ᵇ z) (section y)) ⟩
    f (g x) *ᵇ (f (g y) +ᵇ z)         ≡˘⟨ cong (f (g x) *ᵇ_) (cong (f (g y) +ᵇ_) (section z)) ⟩
    f (g x) *ᵇ (f (g y) +ᵇ f (g z))   ≡˘⟨ cong (f (g x) *ᵇ_) (+-hom (g y) (g z)) ⟩
    f (g x) *ᵇ f (g y +ᵃ g z)         ≡˘⟨ *-hom (g x) (g y +ᵃ g z) ⟩
    f (g x *ᵃ (g y +ᵃ g z))           ≡⟨ cong f (distributeˡ-a (g x) (g y) (g z)) ⟩
    f ((g x *ᵃ g y) +ᵃ (g x *ᵃ g z))  ≡⟨ +-hom (g x *ᵃ g y) (g x *ᵃ g z) ⟩
    f (g x *ᵃ g y) +ᵇ f (g x *ᵃ g z)  ≡⟨ cong (_+ᵇ f (g x *ᵃ g z)) (*-hom (g x) (g y)) ⟩
    (f (g x) *ᵇ f (g y)) +ᵇ f (g x *ᵃ g z) ≡⟨ cong ((f (g x) *ᵇ f (g y)) +ᵇ_) (*-hom (g x) (g z)) ⟩
    (f (g x) *ᵇ f (g y)) +ᵇ (f (g x) *ᵇ f (g z)) ≡⟨ cong (_+ᵇ (f (g x) *ᵇ f (g z))) (cong (_*ᵇ f (g y)) (section x)) ⟩
    (x *ᵇ f (g y)) +ᵇ (f (g x) *ᵇ f (g z)) ≡⟨ cong (_+ᵇ (f (g x) *ᵇ f (g z))) (cong (x *ᵇ_) (section y)) ⟩
    (x *ᵇ y) +ᵇ (f (g x) *ᵇ f (g z))   ≡⟨ cong ((x *ᵇ y) +ᵇ_) (cong (_*ᵇ f (g z)) (section x)) ⟩
    (x *ᵇ y) +ᵇ (x *ᵇ f (g z))         ≡⟨ cong ((x *ᵇ y) +ᵇ_) (cong (x *ᵇ_) (section z)) ⟩
    (x *ᵇ y) +ᵇ (x *ᵇ z)             ∎

  map-distributeʳ-surj : Distributiveʳ _+ᵃ_ _*ᵃ_ → Distributiveʳ _+ᵇ_ _*ᵇ_
  map-distributeʳ-surj distributeʳ-a x y z =
    (y +ᵇ z) *ᵇ x                     ≡˘⟨ cong (λ w → w *ᵇ x) (cong (λ w → w +ᵇ z) (section y)) ⟩
    (f (g y) +ᵇ z) *ᵇ x              ≡˘⟨ cong (λ w → (f (g y) +ᵇ w) *ᵇ x) (section z) ⟩
    (f (g y) +ᵇ f (g z)) *ᵇ x        ≡˘⟨ cong (_*ᵇ x) (+-hom (g y) (g z)) ⟩
    f (g y +ᵃ g z) *ᵇ x              ≡˘⟨ cong (f (g y +ᵃ g z) *ᵇ_) (section x) ⟩
    f (g y +ᵃ g z) *ᵇ f (g x)        ≡˘⟨ *-hom (g y +ᵃ g z) (g x) ⟩
    f ((g y +ᵃ g z) *ᵃ g x)          ≡⟨ cong f (distributeʳ-a (g x) (g y) (g z)) ⟩
    f ((g y *ᵃ g x) +ᵃ (g z *ᵃ g x)) ≡⟨ +-hom (g y *ᵃ g x) (g z *ᵃ g x) ⟩
    f (g y *ᵃ g x) +ᵇ f (g z *ᵃ g x) ≡⟨ cong (_+ᵇ f (g z *ᵃ g x)) (*-hom (g y) (g x)) ⟩
    (f (g y) *ᵇ f (g x)) +ᵇ f (g z *ᵃ g x) ≡⟨ cong ((f (g y) *ᵇ f (g x)) +ᵇ_) (*-hom (g z) (g x)) ⟩
    (f (g y) *ᵇ f (g x)) +ᵇ (f (g z) *ᵇ f (g x)) ≡⟨ cong (_+ᵇ (f (g z) *ᵇ f (g x))) (cong (_*ᵇ f (g x)) (section y)) ⟩
    (y *ᵇ f (g x)) +ᵇ (f (g z) *ᵇ f (g x)) ≡⟨ cong (_+ᵇ (f (g z) *ᵇ f (g x))) (cong (y *ᵇ_) (section x)) ⟩
    (y *ᵇ x) +ᵇ (f (g z) *ᵇ f (g x))   ≡⟨ cong ((y *ᵇ x) +ᵇ_) (cong (_*ᵇ f (g x)) (section z)) ⟩
    (y *ᵇ x) +ᵇ (z *ᵇ f (g x))         ≡⟨ cong ((y *ᵇ x) +ᵇ_) (cong (z *ᵇ_) (section x)) ⟩
    (y *ᵇ x) +ᵇ (z *ᵇ x)             ∎
