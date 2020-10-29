module Prelude where

open import Agda.Builtin.List public
open import Agda.Builtin.Nat public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Float public
open import Agda.Builtin.Word public
open import Agda.Builtin.Char public
open import Agda.Builtin.Equality public

variable
  a b c d e f g h i j k l m n o p q r s t u v w x y z : Set

infix 0 if_then_else_
if_then_else_ : Bool → a → a → a
if true  then t else f = t
if false then t else f = f
