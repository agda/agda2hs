{-# OPTIONS --no-auto-inline #-}

module Haskell.Prim.Num where

open import Agda.Builtin.Nat as Nat hiding (_+_; _-_; _*_; _<_; _==_)
open import Agda.Builtin.Int using (pos; negsuc)
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Agda.Builtin.Unit

open import Haskell.Prim
open import Haskell.Prim.Word
open import Haskell.Prim.Int
open import Haskell.Prim.Integer
open import Haskell.Prim.Double
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Monoid

--------------------------------------------------
-- Num

record Num (a : Set) : Set₁ where
  infixl 6 _+_ _-_
  infixl 7 _*_
  field
    MinusOK       : a → a → Set
    NegateOK      : a → Set
    FromIntegerOK : Integer → Set
    _+_           : a → a → a
    _-_           : (x y : a) → ⦃ MinusOK x y ⦄ → a
    _*_           : a → a → a
    negate        : (x : a) → ⦃ NegateOK x ⦄ → a
    abs           : a → a
    signum        : a → a
    fromInteger   : (n : Integer) → ⦃ FromIntegerOK n ⦄ → a
    overlap ⦃ number ⦄  : Number a
    overlap ⦃ numZero ⦄ : number .Number.Constraint 0
    overlap ⦃ numOne ⦄  : number .Number.Constraint 1

open Num ⦃ ... ⦄ public hiding (FromIntegerOK; number)

{-# COMPILE AGDA2HS Num existing-class #-}

instance
  iNumNat : Num Nat
  iNumNat .MinusOK n m      = IsFalse (n Nat.< m)
  iNumNat .NegateOK 0       = ⊤
  iNumNat .NegateOK (suc _) = ⊥
  iNumNat .Num.FromIntegerOK (negsuc _) = ⊥
  iNumNat .Num.FromIntegerOK (pos _) = ⊤
  iNumNat ._+_ n m = n Nat.+ m
  iNumNat ._-_ n m = n Nat.- m
  iNumNat ._*_ n m = n Nat.* m
  iNumNat .negate n = n
  iNumNat .abs    n = n
  iNumNat .signum 0       = 0
  iNumNat .signum (suc n) = 1
  iNumNat .fromInteger (pos n) = n
  iNumNat .fromInteger (negsuc _) ⦃ () ⦄

  iNumInt : Num Int
  iNumInt .MinusOK _ _         = ⊤
  iNumInt .NegateOK _          = ⊤
  iNumInt .Num.FromIntegerOK _ = ⊤
  iNumInt ._+_ x y             = addInt x y
  iNumInt ._-_ x y             = subInt x y
  iNumInt ._*_ x y             = mulInt x y
  iNumInt .negate x            = negateInt x
  iNumInt .abs x               = absInt x
  iNumInt .signum x            = signInt x
  iNumInt .fromInteger n       = integerToInt n

  iNumInteger : Num Integer
  iNumInteger .MinusOK _ _ = ⊤
  iNumInteger .NegateOK _          = ⊤
  iNumInteger .Num.FromIntegerOK _ = ⊤
  iNumInteger ._+_ x y             = addInteger x y
  iNumInteger ._-_ x y             = subInteger x y
  iNumInteger ._*_ x y             = mulInteger x y
  iNumInteger .negate x            = negateInteger x
  iNumInteger .abs x               = absInteger x
  iNumInteger .signum x            = signInteger x
  iNumInteger .fromInteger n       = n

  iNumWord : Num Word
  iNumWord .MinusOK _ _         = ⊤
  iNumWord .NegateOK _          = ⊤
  iNumWord .Num.FromIntegerOK _ = ⊤
  iNumWord ._+_ x y             = addWord x y
  iNumWord ._-_ x y             = subWord x y
  iNumWord ._*_ x y             = mulWord x y
  iNumWord .negate x            = negateWord x
  iNumWord .abs x               = x
  iNumWord .signum x            = if x == 0 then 0 else 1
  iNumWord .fromInteger n       = integerToWord n

  iNumDouble : Num Double
  iNumDouble .MinusOK _ _         = ⊤
  iNumDouble .NegateOK _          = ⊤
  iNumDouble .Num.FromIntegerOK _ = ⊤
  iNumDouble ._+_ x y             = primFloatPlus x y
  iNumDouble ._-_ x y             = primFloatMinus x y
  iNumDouble ._*_ x y             = primFloatTimes x y
  iNumDouble .negate x            = primFloatMinus 0.0 x
  iNumDouble .abs x               = if x < 0.0 then primFloatMinus 0.0 x else x
  iNumDouble .signum x            = case compare x 0.0 of λ where
                                      LT → -1.0
                                      EQ → x
                                      GT → 1.0
  iNumDouble .fromInteger (pos    n) = fromNat n
  iNumDouble .fromInteger (negsuc n) = fromNeg (suc n)

MonoidSum : ⦃ iNum : Num a ⦄ → Monoid a
MonoidSum .mempty      = 0
MonoidSum .super ._<>_ = _+_

MonoidProduct : ⦃ iNum : Num a ⦄ → Monoid a
MonoidProduct .mempty      = 1
MonoidProduct .super ._<>_ = _*_
