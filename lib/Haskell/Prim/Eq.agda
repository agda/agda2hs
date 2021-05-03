
module Haskell.Prim.Eq where

open import Agda.Builtin.Nat as Nat hiding (_==_)
open import Agda.Builtin.Char
open import Agda.Builtin.Unit
open import Agda.Builtin.List

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Integer
open import Haskell.Prim.Int
open import Haskell.Prim.Word
open import Haskell.Prim.Double
open import Haskell.Prim.Tuple
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either

--------------------------------------------------
-- Eq

record Eq (a : Set) : Set where
  infix 4 _==_ _/=_
  field
    _==_ : a → a → Bool

  _/=_ : a → a → Bool
  x /= y = not (x == y)

open Eq ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Eq existing-class #-}

instance
  iEqNat : Eq Nat
  iEqNat ._==_ = Nat._==_

  iEqInteger : Eq Integer
  iEqInteger ._==_ = eqInteger

  iEqInt : Eq Int
  iEqInt ._==_ = eqInt

  iEqWord : Eq Word
  iEqWord ._==_ = eqWord

  iEqDouble : Eq Double
  iEqDouble ._==_ = primFloatNumericalEquality

  iEqBool : Eq Bool
  iEqBool ._==_ false false = true
  iEqBool ._==_ true  true  = true
  iEqBool ._==_ _     _     = false

  iEqChar : Eq Char
  iEqChar ._==_ = primCharEquality

  iEqUnit : Eq ⊤
  iEqUnit ._==_ _ _ = true

  iEqTuple₀ : Eq (Tuple [])
  iEqTuple₀ ._==_ _ _ = true

  iEqTuple : ∀ {as} → ⦃ Eq a ⦄ → ⦃ Eq (Tuple as) ⦄ → Eq (Tuple (a ∷ as))
  iEqTuple ._==_ (x ∷ xs) (y ∷ ys) = x == y && xs == ys

  iEqList : ⦃ Eq a ⦄ → Eq (List a)
  iEqList ._==_ []       []       = false
  iEqList ._==_ (x ∷ xs) (y ∷ ys) = x == y && xs == ys
  iEqList ._==_ _        _        = false

  iEqMaybe : ⦃ Eq a ⦄ → Eq (Maybe a)
  iEqMaybe ._==_ Nothing  Nothing  = true
  iEqMaybe ._==_ (Just x) (Just y) = x == y
  iEqMaybe ._==_ _        _        = false

  iEqEither : ⦃ Eq a ⦄ → ⦃ Eq b ⦄ → Eq (Either a b)
  iEqEither ._==_ (Left  x) (Left  y) = x == y
  iEqEither ._==_ (Right x) (Right y) = x == y
  iEqEither ._==_ _        _          = false
