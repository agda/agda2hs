module Agda2Hs.Law.Applicative.IO where

open import Haskell.Prim
open import Haskell.Prim.IO

open import Haskell.Prim.Applicative

open import Agda2Hs.Law.Applicative.Def

open import Agda2Hs.Law.Functor.IO

instance postulate iLawfulApplicativeIO : IsLawfulApplicative IO
