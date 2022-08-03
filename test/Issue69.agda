open import Haskell.Prelude

mutual

  data Map (k : Set) (a : Set) : Set where
    Bin : (sz : Nat) → (kx : k) → (x : a)
          → (l : Map k a) → (r : Map k a)
          → {{@0 szVal : sz ≡ (size l) + (size r) + 1}}
          → Map k a
    Tip : Map k a
  {-# COMPILE AGDA2HS Map #-}

  size : {k a : Set} → Map k a → Nat
  size Tip = 0
  size (Bin sz _ _ _ _) = sz
  {-# COMPILE AGDA2HS size #-}
