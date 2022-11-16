open import Haskell.Prelude

data OtherFoo : Set where
  MkFoo : OtherFoo

{-# COMPILE AGDA2HS OtherFoo #-}
