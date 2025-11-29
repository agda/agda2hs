module Records where

open import Haskell.Prim using (Type)
open import Haskell.Prelude using (String; Nat)

variable a b : Type

-- parametrized record type exported as an Haskell record
record Pair (a b : Type) : Type where
  no-eta-equality
  pattern
  constructor MkPair
  field
    proj₁ : a
    proj₂ : b

open Pair public

{-# COMPILE AGDA2HS Pair #-}

-- no named constructor means we reuse the record name

record Wrap (a : Type) : Type where
  no-eta-equality
  pattern
  field unwrap : a
open Wrap public
{-# COMPILE AGDA2HS Wrap #-}

-- record type exported as an Haskell class definition
record MyMonoid (a : Type) : Type where
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

-- record with deriving clause
record User : Type where
  no-eta-equality
  field
    name : String
    code : Nat
open User public
{-# COMPILE AGDA2HS User deriving (Eq, Show) #-}
