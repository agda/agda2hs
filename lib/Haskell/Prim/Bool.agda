
module Haskell.Prim.Bool where

open import Agda.Primitive
open import Agda.Builtin.Bool public

private
  variable
    ℓ : Level

--------------------------------------------------
-- Booleans

infixr 3 _&&_
_&&_ : Bool → Bool → Bool
false && _ = false
true  && x = x

infixr 2 _||_
_||_ : Bool → Bool → Bool
false || x = x
true  || _ = true

not : Bool → Bool
not false = true
not true  = false

otherwise : Bool
otherwise = true
