open import Haskell.Prelude

fmapPair : (a → b) → (c × a) → (c × b)
fmapPair = λ f (x , y) → x , f y

{-# COMPILE AGDA2HS fmapPair #-}
