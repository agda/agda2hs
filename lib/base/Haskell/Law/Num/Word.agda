module Haskell.Law.Num.Word where

open import Haskell.Prim
open import Haskell.Prim.Num
open import Haskell.Prim.Word
open Haskell.Prim.Word.WordInternal

open import Haskell.Law.Equality
open import Haskell.Law.Function
open import Haskell.Law.Nat

open import Haskell.Law.Num.Def
open import Haskell.Law.Num.Nat

open Num iNumNat  renaming (_+_ to _+ⁿ_; _*_ to _*ⁿ_)
open Num iNumWord renaming (_+_ to _+ʷ_; _*_ to _*ʷ_)

-- Word arithmetic wraps around modulo 2⁶⁴, so `w2n` is not a homomorphism from
-- `Word` to `Nat`. Instead we view `Nat` as a quotient of `Word`: the function
-- `n2w` is a surjective homomorphism (it reduces modulo 2⁶⁴), and the ring
-- laws of `Word` are inherited from the ring laws of `Nat` along it.
postulate
  -- Every Word is the image of its value as a natural number under `n2w`.
  n2w∘w2n≡id : ∀ (x : Word)           → n2w (w2n x) ≡ x

  -- `n2w` preserves zero, one, addition and multiplication.
  n2w-0-hom : n2w 0 ≡ 0
  n2w-1-hom : n2w 1 ≡ 1
  n2w-+-hom : Homomorphism₂ _+ⁿ_ _+ʷ_ n2w
  n2w-*-hom : Homomorphism₂ _*ⁿ_ _*ʷ_ n2w

  -- 2⁶⁴ is the upper bound of the ring that forms Words in Nats, so mapping
  -- it back to Word yields zero.
  max-int≡0 : n2w 2⁶⁴ ≡ 0

  -- Words are bounded. They can never be larger than 2⁶⁴.
  bounded : ∀ (x : Word) → w2n x ≤ 2⁶⁴

open Surjection₂
open MonoidSurjection₂

+-wordsAsNats : MonoidSurjection₂ _+ⁿ_ _+ʷ_ n2w w2n 0 0
Surjection₂.hom     (surjection +-wordsAsNats) = n2w-+-hom
Surjection₂.section (surjection +-wordsAsNats) = n2w∘w2n≡id
0-hom +-wordsAsNats = n2w-0-hom

*-wordsAsNats : MonoidSurjection₂ _*ⁿ_ _*ʷ_ n2w w2n 1 1
Surjection₂.hom     (surjection *-wordsAsNats) = n2w-*-hom
Surjection₂.section (surjection *-wordsAsNats) = n2w∘w2n≡id
0-hom *-wordsAsNats = n2w-1-hom

addWord-idˡ : Identityˡ addWord 0
addWord-idˡ = map-idˡ-surj _+ⁿ_ _+ʷ_ n2w w2n 0 0 +-wordsAsNats addNat-idˡ

addWord-idʳ : Identityʳ addWord 0
addWord-idʳ = map-idʳ-surj _+ⁿ_ _+ʷ_ n2w w2n 0 0 +-wordsAsNats addNat-idʳ

addWord-comm : Commutative addWord
addWord-comm = map-comm-surj _+ⁿ_ _+ʷ_ n2w w2n (surjection +-wordsAsNats) addNat-comm

addWord-assoc : Associative addWord
addWord-assoc = map-assoc-surj _+ⁿ_ _+ʷ_ n2w w2n (surjection +-wordsAsNats) addNat-assoc

mulWord-comm : Commutative mulWord
mulWord-comm = map-comm-surj _*ⁿ_ _*ʷ_ n2w w2n (surjection *-wordsAsNats) mulNat-comm

mulWord-assoc : Associative mulWord
mulWord-assoc = map-assoc-surj _*ⁿ_ _*ʷ_ n2w w2n (surjection *-wordsAsNats) mulNat-assoc

mulWord-idˡ : Identityˡ mulWord 1
mulWord-idˡ = map-idˡ-surj _*ⁿ_ _*ʷ_ n2w w2n 1 1 *-wordsAsNats mulNat-idˡ

mulWord-idʳ : Identityʳ mulWord 1
mulWord-idʳ = map-idʳ-surj _*ⁿ_ _*ʷ_ n2w w2n 1 1 *-wordsAsNats mulNat-idʳ

mulWord-distributeˡ-addWord : Distributiveˡ addWord mulWord
mulWord-distributeˡ-addWord = map-distributeˡ-surj _+ⁿ_ _+ʷ_ _*ⁿ_ _*ʷ_ n2w w2n n2w∘w2n≡id n2w-+-hom n2w-*-hom mulNat-distributeˡ-addNat

mulWord-distributeʳ-addWord : Distributiveʳ addWord mulWord
mulWord-distributeʳ-addWord = map-distributeʳ-surj _+ⁿ_ _+ʷ_ _*ⁿ_ _*ʷ_ n2w w2n n2w∘w2n≡id n2w-+-hom n2w-*-hom mulNat-distributeʳ-addNat

neg-inv-word : ∀ (x : Word) → addWord x (negateWord x) ≡ 0
neg-inv-word x =
  begin
    x +ʷ negateWord x
  ≡˘⟨ cong (λ w → w +ʷ negateWord x) (n2w∘w2n≡id x) ⟩
    n2w (w2n x) +ʷ negateWord x
  ≡⟨⟩
    n2w (w2n x) +ʷ n2w (monusNat 2⁶⁴ (w2n x))
  ≡˘⟨ n2w-+-hom (w2n x) (monusNat 2⁶⁴ (w2n x)) ⟩
    n2w (w2n x + monusNat 2⁶⁴ (w2n x))
  ≡⟨ cong n2w (x+[y-x]≡y (w2n x) 2⁶⁴ (bounded x)) ⟩
    n2w 2⁶⁴
  ≡⟨ max-int≡0 ⟩
    0
  ∎

instance
  open IsLawfulNum

  iLawfulNumWord : IsLawfulNum Word
  +-assoc iLawfulNumWord = addWord-assoc
  +-comm iLawfulNumWord = addWord-comm
  +-idˡ iLawfulNumWord = λ x → addWord-idˡ x
  +-idʳ iLawfulNumWord = λ x → addWord-idʳ x
  neg-inv iLawfulNumWord = λ x → neg-inv-word x
  *-assoc iLawfulNumWord = mulWord-assoc
  *-idˡ iLawfulNumWord = λ x → mulWord-idˡ x
  *-idʳ iLawfulNumWord = λ x → mulWord-idʳ x
  distributeˡ iLawfulNumWord = mulWord-distributeˡ-addWord
  distributeʳ iLawfulNumWord = mulWord-distributeʳ-addWord
