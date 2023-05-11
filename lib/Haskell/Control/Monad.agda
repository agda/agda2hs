module Haskell.Control.Monad where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Monad
open import Haskell.Prim.String

guard : {{ MonadFail m }} → (b : Bool) → m (b ≡ True)
guard True = return refl
guard False = fail "Guard was not True"
