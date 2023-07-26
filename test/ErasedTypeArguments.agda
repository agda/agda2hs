-- Testing whether erased value arguments in type signatures
-- do get erased.
module ErasedTypeArguments where

open import Agda.Primitive

-- A record type which has both members compiled,
-- but the argument of the lambda is erased;
-- so that it won't be dependent-typed after compilation.
record Σ' {i j} (a : Set i) (b : @0 a → Set j) : Set (i ⊔ j) where
  constructor _:^:_                      -- see https://stackoverflow.com/questions/10548170/what-characters-are-permitted-for-haskell-operators
  field
    proj₁ : a
    proj₂ : b proj₁
open Σ' public
infixr 4 _:^:_
{-# COMPILE AGDA2HS Σ' #-}
