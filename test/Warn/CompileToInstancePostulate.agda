open import Haskell.Prelude
open import Vec

-- A postulated instance has no definition, so its consistency with the target
-- instance cannot be checked.
postulate instance iEqVec : {a : Set} {n : Nat} → {{Eq a}} → Eq (Vec a n)

{-# COMPILE AGDA2HS iEqVec to iEqList #-}
