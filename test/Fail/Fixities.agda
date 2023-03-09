module Fail.Fixities where

open import Haskell.Prelude

infixl 8.5 _<+>_
_<+>_ : Int → Int → Int
x <+> y = x

{-# COMPILE AGDA2HS _<+>_ #-}
