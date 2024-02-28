
module Haskell.Prim.String where

open import Haskell.Prim
open import Haskell.Prim.List
open import Haskell.Prim.Foldable

--------------------------------------------------
-- String
-- This is _not_ the builtin String type of Agda;
-- which is defined by postulates.
-- fromString can be used to produce Haskell strings
-- from that.

String = List Char

instance
  iIsStringString : IsString String
  iIsStringString .IsString.Constraint _ = ⊤
  iIsStringString .fromString s = primStringToList s

private
  cons : Char → List String → List String
  cons c []       = (c ∷ []) ∷ []
  cons c (s ∷ ss) = (c ∷ s) ∷ ss

lines : String → List String
lines []         = []
lines ('\n' ∷ s) = [] ∷ lines s
lines (c    ∷ s) = cons c (lines s)

private
 mutual
  space : String → List String
  space [] = []
  space (c ∷ s) = if primIsSpace c then space s else cons c (word s)

  word  : String → List String
  word []      = []
  word (c ∷ s) = if primIsSpace c then [] ∷ space s else cons c (word s)

words : String → List String
words [] = []
words s@(c ∷ s₁) = if primIsSpace c then space s₁ else word s

unlines : List String → String
unlines = concatMap (_++ "\n")

unwords : List String → String
unwords [] = ""
unwords (w ∷ []) = w
unwords (w ∷ ws) = w ++ ' ' ∷ unwords ws
