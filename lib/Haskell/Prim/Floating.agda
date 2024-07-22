module Haskell.Prim.Floating where

open import Haskell.Prim

--------------------------------------------------
-- Floating

record Floating (a : Set) : Set where
  infixr 8 _**_
  field
	pi      : a
	exp     : a → a
	log     : a → a
	sqrt	: a → a
	_**_    : Floating → Floating → Floating
	logBase : Floating → Floating → Floating
	sin     : a → a
	cos     : a → a
	tan		: a → a
	asin    : a → a
	acos    : a → a
	atan    : a → a
	sinh    : a → a
	cosh    : a → a
	tanh    : a → a
	asinh   : a → a
	acosh   : a → a
	atanh   : a → a
open Floating ⦃... ⦄  public

{-# COMPILE AGDA2HS Floating existing-class #-}

