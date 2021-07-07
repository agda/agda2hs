
module Fail.NonCopatternInstance where

record HasId (a : Set) : Set where
  field id : a → a

open HasId ⦃ ... ⦄

{-# COMPILE AGDA2HS HasId class #-}

data Unit : Set where
  MkUnit : Unit

{-# COMPILE AGDA2HS Unit #-}

instance
  UnitHasId : HasId Unit
  UnitHasId = r                     -- NOT CORRECT
    where r = record {id = λ x → x}
  -- UnitHasId .id x = x                -- CORRECT
  -- UnitHasId = record {id = λ x → x}  -- CORRECT

{-# COMPILE AGDA2HS UnitHasId #-}
