module LawfulNum where

open import Haskell.Prelude
open import Haskell.Law.Num

-- Regression test for https://github.com/agda/agda2hs/issues/499.
-- `Word` arithmetic wraps around modulo 2⁶⁴, so `w2n` is not a homomorphism
-- from `Word` to `Nat`. The ring laws for `Word` are instead derived from the
-- fact that `n2w` is a surjective homomorphism from `Nat`, which is sound.

wordAddComm : ∀ (x y : Word) → x + y ≡ y + x
wordAddComm = IsLawfulNum.+-comm iLawfulNumWord

wordAddAssoc : ∀ (x y z : Word) → (x + y) + z ≡ x + (y + z)
wordAddAssoc = IsLawfulNum.+-assoc iLawfulNumWord

wordNegInv : ∀ (x : Word) → x + negate x ≡ 0
wordNegInv = neg-inv-word

wordMulDistribˡ : ∀ (x y z : Word) → x * (y + z) ≡ (x * y) + (x * z)
wordMulDistribˡ = IsLawfulNum.distributeˡ iLawfulNumWord

natLawful : IsLawfulNum Nat
natLawful = iLawfulNumNat
