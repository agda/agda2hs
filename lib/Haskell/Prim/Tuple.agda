
module Haskell.Prim.Tuple where

open import Agda.Builtin.List

open import Haskell.Prim

variable
  @0 as : List Set

--------------------------------------------------
-- Tuples

infixr 5 _∷_
data Tuple : List Set → Set where
  []  : Tuple []
  _∷_ : a → Tuple as → Tuple (a ∷ as)

infix 3 _×_ _×_×_

_×_ : (a b : Set) → Set
a × b = Tuple (a ∷ b ∷ [])

_×_×_ : (a b c : Set) → Set
a × b × c = Tuple (a ∷ b ∷ c ∷ [])

infix -1 _,_ _,_,_

pattern _,_     x y     = x Tuple.∷ y Tuple.∷ []
pattern _,_,_   x y z   = x Tuple.∷ y Tuple.∷ z Tuple.∷ []

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
