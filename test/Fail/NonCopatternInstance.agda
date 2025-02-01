
module Fail.NonCopatternInstance where

open import Haskell.Prim using (Type)

record HasId (a : Type) : Type where
  field id : a → a

open HasId ⦃ ... ⦄

{-# COMPILE AGDA2HS HasId class #-}

data Unit : Type where
  MkUnit : Unit

{-# COMPILE AGDA2HS Unit #-}

instance
  UnitHasId : HasId Unit
  UnitHasId = r                     -- NOT CORRECT
    where r = record {id = λ x → x}
  -- UnitHasId .id x = x                -- CORRECT
  -- UnitHasId = record {id = λ x → x}  -- CORRECT

{-# COMPILE AGDA2HS UnitHasId #-}
