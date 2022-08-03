
module Haskell.Prim.Bool where

open import Haskell.Prim

--------------------------------------------------
-- Booleans

infixr 3 _&&_
_&&_ : Bool → Bool → Bool
False && _ = False
True  && x = x

infixr 2 _||_
_||_ : Bool → Bool → Bool
False || x = x
True  || _ = True

not : Bool → Bool
not False = True
not True  = False

otherwise : Bool
otherwise = True
