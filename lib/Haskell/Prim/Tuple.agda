
module Haskell.Prim.Tuple where

open import Haskell.Prim

--------------------------------------------------
-- Tuples

infix 3 _×_ _×_×_

infix -1 _,_ _,_,_

record _×_ (a b : Set) : Set where
  constructor _,_
  field
    fst : a
    snd : b
open _×_ public

data _×_×_ (a b c : Set) : Set where
  _,_,_ : a → b → c → a × b × c

uncurry : (a → b → c) → a × b → c
uncurry f (x , y) = f x y

curry : (a × b → c) → a → b → c
curry f x y = f (x , y)

first : (a → b) → a × c → b × c
first f (x , y) = f x , y

second : (a → b) → c × a → c × b
second f (x , y) = x , f y

_***_ : (a → b) → (c → d) → a × c → b × d
(f *** g) (x , y) = f x , g y
