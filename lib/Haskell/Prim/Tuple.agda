
module Haskell.Prim.Tuple where

open import Haskell.Prim

variable
  @0 as : List Set

--------------------------------------------------
-- Tuples

infixr 5 _;_
record Pair (A B : Set) : Set where
  constructor _;_
  field fst : A ; snd : B

Tuple : List Set → Set
Tuple [] = ⊤
Tuple (A ∷ AS) = Pair A (Tuple AS)

infix 3 _×_ _×_×_

_×_ : (a b : Set) → Set
a × b = Tuple (a ∷ b ∷ [])

_×_×_ : (a b c : Set) → Set
a × b × c = Tuple (a ∷ b ∷ c ∷ [])

infix -1 _,_ _,_,_

pattern _,_     x y     = x ; y ; tt
pattern _,_,_   x y z   = x ; y ; z ; tt

uncurry : (a → b → c) → a × b → c
uncurry f (x , y) = f x y

curry : (a × b → c) → a → b → c
curry f x y = f (x , y)

fst : a × b → a
fst (x , _) = x

snd : a × b → b
snd (_ , y) = y

first : (a → b) → a × c → b × c
first f (x , y) = f x , y

second : (a → b) → c × a → c × b
second f (x , y) = x , f y

_***_ : (a → b) → (c → d) → a × c → b × d
(f *** g) (x , y) = f x , g y
