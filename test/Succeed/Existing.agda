module Existing where

open import Haskell.Prelude

-- Definitions with a `COMPILE AGDA2HS ... existing` pragma are not compiled by
-- agda2hs; their Haskell implementation is expected to be provided through a
-- FOREIGN pragma, either as an inline definition or through an import.
{-# FOREIGN AGDA2HS
import Data.Char (ord)

existingFun :: Int
existingFun = 42

data ExistingData = MkExistingData Int

class ExistingClass a where
  existingMethod :: a -> Int

type ExistingType = Int
#-}

-- An inline Haskell definition.
existingFun : Int
existingFun = 0
{-# COMPILE AGDA2HS existingFun existing #-}

-- An inline Haskell datatype definition.
data ExistingData : Type where
  MkExistingData : Int -> ExistingData
{-# COMPILE AGDA2HS ExistingData existing #-}

-- An inline Haskell class definition.
record ExistingClass (a : Type) : Type where
  field
    existingMethod : a → Int
{-# COMPILE AGDA2HS ExistingClass existing-class #-}

-- An inline Haskell type synonym.
ExistingType : Type
ExistingType = Int
{-# COMPILE AGDA2HS ExistingType existing #-}

-- A postulate implemented by importing a Haskell function in the FOREIGN block.
postulate
  ord : Char → Int
{-# COMPILE AGDA2HS ord existing #-}

-- The `existing` definitions can still be used from compiled code.
useExisting : Int → Int
useExisting x = existingFun + x
{-# COMPILE AGDA2HS useExisting #-}
