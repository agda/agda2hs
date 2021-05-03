module Records where

variable
  a b : Set

-- parametrized record type exported as an Haskell record
record Pair (a b : Set) : Set where
  constructor MkPair
  field
    proj₁ : a
    proj₂ : b

open Pair public

{-# COMPILE AGDA2HS Pair #-}

-- no named constructor means we reuse the record name

record Wrap (a : Set) : Set where
  field
    unwrap : a

open Wrap public

{-# COMPILE AGDA2HS Wrap #-}

-- record type exported as an Haskell class definition
record MyMonoid (a : Set) : Set where
  field
    mempty  : a
    mappend : a → a → a

{-# COMPILE AGDA2HS MyMonoid class #-}

swap : Pair a b → Pair b a
swap (MkPair x y) = MkPair y x

swap₂ : Wrap (Pair a b) → Wrap (Pair b a)
swap₂ (record {unwrap = p}) = record {unwrap = record { proj₁ = proj₂ p; proj₂ = p .proj₁ } }

{-# COMPILE AGDA2HS swap #-}
{-# COMPILE AGDA2HS swap₂ #-}
