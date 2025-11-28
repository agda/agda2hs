module IOInput where

open import Haskell.Prelude

main : IO ⊤
main = do putStrLn "Write something "
          x ← getLine
          putStr $ "You wrote: " ++ x
          return tt

{-# COMPILE AGDA2HS main #-}
