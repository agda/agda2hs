module Haskell.Law.Num.Def where

open import Haskell.Prim
open import Haskell.Prim.Num
open import Haskell.Prim.Integer

record IsLawfulNum (a : Type) ⦃ iNum : Num a ⦄ : Type₁ where
  field
    +-assoc : ∀ (x y z : a) → (x + y) + z ≡ x + (y + z)

    +-comm : ∀ (x y : a) → x + y ≡ y + x

    +-idˡ : ∀ (x : a) {{@0 _ : Num.FromIntegerOK iNum 0}}
      → fromInteger 0 + x ≡ x
    +-idʳ : ∀ (x : a) {{@0 _ : Num.FromIntegerOK iNum 0}}
      → x + fromInteger 0 ≡ x

    neg-inv : ∀ (x : a) {{@0 _ : Num.FromIntegerOK iNum 0}} {{@0 _ : Num.NegateOK iNum x}}
      → x + negate x ≡ fromInteger 0

    *-assoc : ∀ (x y z : a) → (x * y) * z ≡ x * (y * z)

    *-idˡ : ∀ (x : a) {{@0 _ : Num.FromIntegerOK iNum 1}}
      → fromInteger 1 * x ≡ x
    *-idʳ : ∀ (x : a) {{@0 _ : Num.FromIntegerOK iNum 1}}
      → x * fromInteger 1 ≡ x

    distributeˡ : ∀ (x y z : a) → x * (y + z) ≡ (x * y) + (x * z)
    distributeʳ : ∀ (x y z : a) → (y + z) * x ≡ (y * x) + (z * x)

    -- We are currently missing the following because toInteger is missing in our Prelude.
    -- "if the type also implements Integral, then fromInteger is a left inverse for toInteger, i.e. fromInteger (toInteger i) == i"
open IsLawfulNum ⦃ ... ⦄ public

open import Haskell.Law.Equality
open import Haskell.Law.Function

{-|
A number homomorphism establishes a homomorphism from one Num type a to another one b.
In particular, zero and one are mapped to zero and one in the other Num type,
and addition, multiplication, and negation are homorphic.
-}
record NumHomomorphism (a b : Type) ⦃ iNuma : Num a ⦄ ⦃ iNumb : Num b ⦄ (φ : a → b) : Type where
  0ᵃ = Num.fromInteger iNuma (pos 0)
  0ᵇ = Num.fromInteger iNumb (pos 0)
  1ᵃ = Num.fromInteger iNuma (pos 1)
  1ᵇ = Num.fromInteger iNumb (pos 1)

  field
    +-hom : Homomorphism₂ _+_ _+_ φ
    *-hom : Homomorphism₂ _*_ _*_ φ
    ⦃ minus-ok ⦄       : ∀ {x y : a}     → ⦃ MinusOK x y ⦄               → MinusOK (φ x) (φ y)
    ⦃ negate-ok ⦄      : ∀ {x   : a}     → ⦃ NegateOK x ⦄                → NegateOK (φ x)
    ⦃ fromInteger-ok ⦄ : ∀ {i : Integer} → ⦃ Num.FromIntegerOK iNuma i ⦄ → Num.FromIntegerOK iNumb i
    0-hom : ⦃ @0 _ : Num.FromIntegerOK iNuma (pos 0) ⦄ → φ 0ᵃ ≡ 0ᵇ
    1-hom : ⦃ @0 _ : Num.FromIntegerOK iNuma (pos 1) ⦄ → φ 1ᵃ ≡ 1ᵇ
    negate-hom : ∀ (x : a) → ⦃ @0 _ : Num.NegateOK iNuma x ⦄ → φ (negate x) ≡ negate (φ x) --Homomorphism₁ inlined for type instances

{-|
A number embedding is an invertible number homomorphism.
-}
record NumEmbedding (a b : Type) ⦃ iNuma : Num a ⦄ ⦃ iNumb : Num b ⦄ (φ : a → b) (φ⁻¹ : b → a) : Type where
  field
    hom   : NumHomomorphism a b φ
    embed : φ⁻¹ ∘ φ ≗ id

  open NumHomomorphism hom

  +-Embedding₂ : Embedding₂ _+_ _+_ φ φ⁻¹
  Embedding₂.hom   +-Embedding₂ = +-hom
  Embedding₂.embed +-Embedding₂ = embed

  *-Embedding₂ : Embedding₂ _*_ _*_ φ φ⁻¹
  Embedding₂.hom   *-Embedding₂ = *-hom
  Embedding₂.embed *-Embedding₂ = embed

  +-MonoidEmbedding₂ : ⦃ @0 _ : Num.FromIntegerOK iNuma (pos 0) ⦄ → MonoidEmbedding₂ _+_ _+_ φ φ⁻¹ 0ᵃ 0ᵇ
  MonoidEmbedding₂.embedding +-MonoidEmbedding₂ = +-Embedding₂
  MonoidEmbedding₂.0-hom     +-MonoidEmbedding₂ = 0-hom

  *-MonoidEmbedding₂ : ⦃ @0 _ : Num.FromIntegerOK iNuma (pos 1) ⦄ → MonoidEmbedding₂ _*_ _*_ φ φ⁻¹ 1ᵃ 1ᵇ
  MonoidEmbedding₂.embedding *-MonoidEmbedding₂ = *-Embedding₂
  MonoidEmbedding₂.0-hom     *-MonoidEmbedding₂ = 1-hom

{-|
Given an embedding from one number type a onto another one b,
we can conclude that b satisfies the laws of Num if a satisfies the
laws of Num.
-}
map-IsLawfulNum : ∀ {a b : Type} ⦃ iNuma : Num a ⦄ ⦃ iNumb : Num b ⦄
  → (a2b : a → b) (b2a : b → a)
  → NumEmbedding a b a2b b2a
  → IsLawfulNum b
    -----------------------
  → IsLawfulNum a
map-IsLawfulNum {a} {b} {{numa}} {{numb}} f g proj lawb =
  record
  { +-assoc = map-assoc _+ᵃ_ _+ᵇ_ f g +-Embedding₂ (+-assoc lawb)
  ; +-comm  = map-comm  _+ᵃ_ _+ᵇ_ f g +-Embedding₂ (+-comm lawb)
  ; +-idˡ = λ x → map-idˡ _+ᵃ_ _+ᵇ_ f g 0ᵃ 0ᵇ +-MonoidEmbedding₂ (λ y → +-idˡ lawb y) x
  ; +-idʳ = λ x → map-idʳ _+ᵃ_ _+ᵇ_ f g 0ᵃ 0ᵇ +-MonoidEmbedding₂ (λ y → +-idʳ lawb y) x
  ; neg-inv = map-neg-inv
  ; *-assoc = map-assoc _*ᵃ_ _*ᵇ_ f g *-Embedding₂ (*-assoc lawb)
  ; *-idˡ = λ x → map-idˡ _*ᵃ_ _*ᵇ_ f g 1ᵃ 1ᵇ *-MonoidEmbedding₂ (λ y → *-idˡ lawb y) x
  ; *-idʳ = λ x → map-idʳ _*ᵃ_ _*ᵇ_ f g 1ᵃ 1ᵇ *-MonoidEmbedding₂ (λ y → *-idʳ lawb y) x
  ; distributeˡ = map-distributeˡ _+ᵃ_ _+ᵇ_ _*ᵃ_ _*ᵇ_ f g embed +-hom *-hom (distributeˡ lawb)
  ; distributeʳ = map-distributeʳ _+ᵃ_ _+ᵇ_ _*ᵃ_ _*ᵇ_ f g embed +-hom *-hom (distributeʳ lawb)
  }
  where
    open NumEmbedding proj
    open NumHomomorphism hom
    open IsLawfulNum lawb
    open Num numa renaming (_+_ to _+ᵃ_; _*_ to _*ᵃ_; negate to negateᵃ)
    open Num numb renaming (_+_ to _+ᵇ_; _*_ to _*ᵇ_; negate to negateᵇ)

    map-neg-inv : ∀ (x : a) ⦃ @0 _ : Num.FromIntegerOK numa (pos 0) ⦄ ⦃ @0 _ : Num.NegateOK numa x ⦄
      → x +ᵃ negateᵃ x ≡ 0ᵃ
    map-neg-inv x =
      x +ᵃ negateᵃ x           ≡˘⟨ embed (x +ᵃ negateᵃ x) ⟩
      g (f (x +ᵃ negateᵃ x))   ≡⟨ cong g (+-hom x (negateᵃ x)) ⟩
      g (f x +ᵇ f (negateᵃ x)) ≡⟨ cong g (cong (f x +ᵇ_) (negate-hom x)) ⟩
      g (f x +ᵇ negateᵇ (f x)) ≡⟨ cong g (neg-inv lawb (f x)) ⟩
      g 0ᵇ                     ≡˘⟨ cong g 0-hom ⟩
      g (f 0ᵃ)                 ≡⟨ embed 0ᵃ ⟩
      0ᵃ ∎
