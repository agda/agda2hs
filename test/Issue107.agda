
open import Haskell.Prelude

testMax : (x y : Nat) → max (suc x) (suc y) ≡ suc (max x y)
testMax x y = refl

testMin : (x y : Nat) → min (suc x) (suc y) ≡ suc (min x y)
testMin x y = refl
