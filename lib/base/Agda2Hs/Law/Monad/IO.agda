module Agda2Hs.Law.Monad.IO where

open import Haskell.Prim
open import Haskell.Prim.IO

open import Haskell.Prim.Monad

open import Agda2Hs.Law.Monad.Def

open import Agda2Hs.Law.Applicative.IO using (iLawfulApplicativeIO)

instance
  postulate
    iPreLawfulMonadIO : PreLawfulMonad IO

  iIsLawfulMonadIO : IsLawfulMonad IO
  iIsLawfulMonadIO = record { applicative = iLawfulApplicativeIO }
