open import Haskell.Prelude

data Void : Type where

test : Maybe Void → Maybe Void
test = λ
    { Nothing → Nothing
    }

{-# COMPILE AGDA2HS Void #-}
{-# COMPILE AGDA2HS test #-}
