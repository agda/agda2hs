module Haskell.Law.Monad.IO where

open import Haskell.Prim
open import Haskell.Prim.IO

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def

open import Haskell.Law.Applicative.IO using (iLawfulApplicativeIO)

instance
  postulate
    iIsDefaultMonadIO : IsDefaultMonad IO
    iMonadLawsIO : MonadLaws IO

  iIsLawfulMonadIO : IsLawfulMonad IO
  iIsLawfulMonadIO = record { applicative = iLawfulApplicativeIO }
