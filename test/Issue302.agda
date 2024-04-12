open import Haskell.Prelude

not0 : Int → Bool
not0 n = n /= 0
{-# COMPILE AGDA2HS not0 #-}
