-- Testing whether erased value arguments in record type signatures
-- and in lambdas do get erased.
module ErasedTypeArguments where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

-- A record type which has both members compiled,
-- but the argument of the lambda is erased;
-- so that it won't be dependent-typed after compilation.
record Σ' {i j} (a : Set i) (b : @0 a -> Set j) : Set (i ⊔ j) where
  constructor _:^:_
  field
    proj₁ : a
    proj₂ : b proj₁
open Σ' public
infixr 4 _:^:_
{-# COMPILE AGDA2HS Σ' #-}

-- Now test lambdas.
-- Actually, Agda can deduce here that n is erased; probably from the type signature of Σ'.
test : Nat -> Σ' Nat (λ (n : Nat) -> ⊤)
test n = n :^: tt
{-# COMPILE AGDA2HS test #-}

-- Tests a type function that would be accepted anyway,
-- but the argument is erased.
data Id {i j} (@0 a : Set i) (f : @0 Set i -> Set j) : Set j where
  MkId : f a -> Id a f
{-# COMPILE AGDA2HS Id newtype #-}
