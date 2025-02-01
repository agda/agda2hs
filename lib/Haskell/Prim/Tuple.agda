
module Haskell.Prim.Tuple where

open import Haskell.Prim

--------------------------------------------------
-- Tuples

infix 3 _×_ _×_×_

infix -1 _,_ _,_,_

record _×_ (a b : Type) : Type where
  constructor _,_
  field
    fst : a
    snd : b
open _×_ public

{-# COMPILE AGDA2HS _×_ tuple #-}

record _×_×_ (a b c : Type) : Type where
  no-eta-equality; pattern
  constructor _,_,_
  field
    fst3 : a
    snd3 : b
    thd3 : c

{-# COMPILE AGDA2HS _×_×_ tuple #-}

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
