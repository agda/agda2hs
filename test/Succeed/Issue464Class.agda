{-# OPTIONS --erasure #-}
module Issue464Class where

open import Haskell.Prelude

-- one method

record Default (a : Type) : Type where
  field
    def : a

open Default ⦃ ... ⦄ public

-- two methods

{-# COMPILE AGDA2HS Default class #-}

record TwoMethods (a : Type) : Type where
  field
    methodOne : a
    methodTwo : a

open TwoMethods ⦃ ... ⦄ public

{-# COMPILE AGDA2HS TwoMethods class #-}

-- instance using a record

record Projected (a : Type) : Type where
  field
    projected : a

record ProjectedMin (a : Type) : Type where
  field
    projected : a

open Projected ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Projected class ProjectedMin #-}
