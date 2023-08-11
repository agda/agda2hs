module IOFile where

open import Haskell.Prelude

main : IO ⊤
main = do file ← readFile "IOFile.agda"
          writeFile "IOFile2.agda" file
          appendFile "IOFile2.agda" "-- Written by appendFile"
          file2 ← readFile "IOFile2.agda"
          print file2
          return tt
          
{-# COMPILE AGDA2HS main #-}
