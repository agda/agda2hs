open import Haskell.Prelude

data OtherFoo : Type where
  MkFoo : OtherFoo

{-# COMPILE AGDA2HS OtherFoo #-}
