module Issue94 where

open import Haskell.Prelude

thing : List a → List a
thing xs = aux xs
  where
    aux : List a → List a
    aux xs = xs
{-# COMPILE AGDA2HS thing #-}
