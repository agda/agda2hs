module Haskell.Control.Monad where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Monad
open import Haskell.Prim.String
open import Haskell.Extra.Erase

guard : {{ MonadFail m }} → (b : Bool) → m (Erase (b ≡ True))
guard True = return (Erased refl)
guard False = fail "Guard was not True"
