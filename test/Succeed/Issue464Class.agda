{-# OPTIONS --erasure #-}
module Issue464Class where

open import Haskell.Prelude

record Default (a : Type) : Type where
  field
    def : a

open Default ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Default class #-}

record TwoMethods (a : Type) : Type where
  field
    methodOne : a
    methodTwo : a

open TwoMethods ⦃ ... ⦄ public

{-# COMPILE AGDA2HS TwoMethods class #-}
