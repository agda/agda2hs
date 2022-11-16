
module Fail.InvalidName where

open import Haskell.Prelude

F : Int → Int
F x = x

{-# COMPILE AGDA2HS F #-}
