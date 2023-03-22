
open import Haskell.Prelude hiding (max)

subst : (@0 p : @0 a → Set) {@0 m n : a} → @0 m ≡ n → p m → p n
subst p refl t = t

{-# COMPILE AGDA2HS subst transparent #-}

max : Nat → Nat → Nat
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)

data Tree (a : Set) : (@0 height : Nat) → Set where
  Tip : Tree a 0
  Bin : ∀ {@0 l r} (x : a) → Tree a l → Tree a r → Tree a (suc (max l r))

{-# COMPILE AGDA2HS Tree #-}

@0 max-comm : (@0 l r : Nat) → max l r ≡ max r l
max-comm zero zero = refl
max-comm zero (suc r) = refl
max-comm (suc l) zero = refl
max-comm (suc l) (suc r) = cong suc (max-comm l r)

mirror : ∀ {@0 h} → Tree a h → Tree a h
mirror Tip = Tip
mirror {a = a} (Bin {l} {r} x lt rt) =
  subst (Tree a) (cong suc (max-comm r l)) (Bin x (mirror rt) (mirror lt))

{-# COMPILE AGDA2HS mirror #-}
