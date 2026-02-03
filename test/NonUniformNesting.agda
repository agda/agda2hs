
open import Agda.Builtin.Nat

variable
  A B C D : Set
  k l m n : Nat

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

data PList (A : Set) : Nat → Set where
  [] : PList A zero
  _∷_ : A → PList (A × A) n → PList A (suc n)

data RoseTree (A : Set) : Nat → Set where
  leaf : A → RoseTree A zero
  node : PList (RoseTree A m) n → RoseTree A (suc m)

_***_ : (A → B) → (C → D) → A × C → B × D
(f *** g) (x , y) = f x , g y

map : (A → B) → PList A n → PList B n
map f [] = []
map f (x ∷ xs) = f x ∷ map (f *** f) xs

unzip : {A B : Set} → PList (A × B) n → PList A n × PList B n
unzip zs = map fst zs , map snd zs

sum : RoseTree Nat m → Nat
suml : PList (RoseTree Nat m) n → Nat

sum (leaf x) = x
sum (node x) = suml x

suml [] = 0
suml (x ∷ xs) = sum x + let (xs , ys) = unzip xs in suml xs + suml ys
