
open import Haskell.Prelude

module _ (@0 n : Bool) where

record R : Set where
  field
    fld : Int
open R public

{-# COMPILE AGDA2HS R #-}

foo : R → Int
foo x = fld x

{-# COMPILE AGDA2HS foo #-}
