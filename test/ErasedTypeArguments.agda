-- Testing whether erased value arguments in record type signatures
-- and in lambdas do get erased.
module ErasedTypeArguments where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

-- A record type which has both members compiled,
-- but the argument of the lambda is erased;
-- so that it won't be dependent-typed after compilation.
record Σ' {i j} (a : Type i) (b : @0 a -> Type j) : Type (i ⊔ j) where
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
data Id {i j} (@0 a : Type i) (f : @0 Type i -> Type j) : Type j where
  MkId : f a -> Id a f
{-# COMPILE AGDA2HS Id newtype #-}
