
module Haskell.Prim.String where

open import Haskell.Prim


--------------------------------------------------
-- String

-- This is _not_ the builtin String type of Agda
-- which is defined by postulates.
-- `fromString` can be used to convert back
-- to builtin Agda strings.
String = List Char

instance
  iIsStringString : IsString String
  iIsStringString .IsString.Constraint _ = ⊤
  iIsStringString .fromString s = primStringToList s
