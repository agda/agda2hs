module PreludeHiding where

open import Haskell.Prelude

fromIntegral : Int → Int
fromIntegral x = x

{-# COMPILE AGDA2HS fromIntegral #-}
