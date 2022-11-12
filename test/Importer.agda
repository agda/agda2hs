open import Haskell.Prelude
open import Importee

bar : Int
bar = foo

{-# COMPILE AGDA2HS bar #-}
