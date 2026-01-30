module EqualityExample where

open import Haskell.Prelude
open import Agda.Primitive using (Level)

variable @0 ℓ : Level
coerce' : {@0 a b : Type} → ⦃ @0 _ : a ≡ b ⦄ → a → b
coerce' ⦃ refl ⦄ x = x
{-# COMPILE AGDA2HS coerce' #-}

instance
  symType : {@0 a b : Type ℓ} → ⦃ @0 p : a ≡ b ⦄ → b ≡ a
  symType ⦃ refl ⦄ = refl

-- A function that requires two types to be equal to return a list of them.
-- In Haskell, this corresponds to:
-- sameList :: (a ~ b) => a -> b -> [a]
-- sameList x y = [x, y]
sameList : {@0 x y : Type} → ⦃ @0 p : x ≡ y ⦄ → x → y → List x
sameList {x} {y} {{p}} vx vy = vx ∷ coerce' ⦃ symType ⦃ p ⦄ ⦄ vy ∷ []
{-# COMPILE AGDA2HS sameList #-}
