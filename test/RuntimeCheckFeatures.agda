{-# OPTIONS --sized-types #-}
module RuntimeCheckFeatures where

open import Haskell.Prelude
open import Haskell.Extra.Delay
open import Haskell.Extra.Erase
open import Haskell.Extra.Dec.Instances

noneErasedFun : Nat → Nat
noneErasedFun _ = 1
{-# COMPILE AGDA2HS noneErasedFun #-}

noDecInstance : ⦃ x : Nat ⦄ → @0 ⦃ HasResult x (now x) ⦄ → Nat
noDecInstance = 0
{-# COMPILE AGDA2HS noDecInstance #-}

simpleFun : (x : Nat) → @0 ⦃ IsTrue (x > 0) ⦄ → Nat
simpleFun _ = 0
{-# COMPILE AGDA2HS simpleFun #-}

simpleFunCaller : Nat
simpleFunCaller = simpleFun 1
{-# COMPILE AGDA2HS simpleFunCaller #-}

-- Even precondition
singleEven : ((x : Nat) → @0 IsTrue (x > 0) → Nat) → Nat
singleEven _ = 0
{-# COMPILE AGDA2HS singleEven #-}

-- Double odd precondition with backreferencing and same-level nested checks
doubleOdd : (x : Nat) → (((y : Nat) → @0 IsFalse (x < y) → Nat) → Nat) → (((y : Nat) → @0 IsFalse (x < y) → Nat) → Nat) → Nat
doubleOdd _ _ _ = 0
{-# COMPILE AGDA2HS doubleOdd #-}

-- Triple odd precondition with multi-level checks
tripleOdd : (((m : Nat) → @0 IsTrue (m > 0) → (((n : Nat) → @0 IsFalse (n < 1) → Nat) → Nat) → Nat) → Nat) → Nat
tripleOdd _ = 0
{-# COMPILE AGDA2HS tripleOdd #-}

-- If you want to deconstruct in Haskell, you have to write deconstructors in Agda.
-- Making the constructor available would enable bypassing the smart constructor.
data Dat : Set where
  Con : (x : Nat) → @0 IsTrue (x > 0) → Dat
  NoneErasedCon : Nat → Dat
{-# COMPILE AGDA2HS Dat #-}

-- Term variables in type parameter not supported, so not showcased here
record Rec : Set where
  field
    recFst : Nat
    recSnd : @0 IsTrue (recFst > 0) → Nat
open Rec public
{-# COMPILE AGDA2HS Rec #-}

record Newt : Set where
  field
    theField : (x : Nat) → @0 IsTrue (x > 0) → Nat
open Newt public
{-# COMPILE AGDA2HS Newt newtype #-}

record NoneErasedNewt : Set where
  field
    noneErasedField : Nat
open NoneErasedNewt public
{-# COMPILE AGDA2HS NoneErasedNewt newtype #-}

record ErasedField : Set where
  field
    erasedFst : Nat
    @0 erasedSnd : IsTrue (erasedFst > 0)
open ErasedField public
{-# COMPILE AGDA2HS ErasedField #-}

-- Should not be exported due to erased within
listErased : (fs : List (((n : Nat) → @0 ⦃ IsFalse (n < 1) ⦄ → Nat) → Nat)) → Nat
listErased _ = 0
{-# COMPILE AGDA2HS listErased #-}

-- Should not be exported due to erased (part of TCB)
eraseTCB : (n : Nat) → @0 Erase (IsFalse (1 < n)) → Nat
eraseTCB n iErased = 0
{-# COMPILE AGDA2HS eraseTCB #-}

-- Should be exported despite TCB record containing an erasure because erasure is not in a critical position
fUnzip : {a b : Set} {f : Set → Set} → ⦃ Functor f ⦄ → f (a × b) → (f a × f b)
fUnzip xs = (fmap fst xs , fmap snd xs)
{-# COMPILE AGDA2HS fUnzip #-}
