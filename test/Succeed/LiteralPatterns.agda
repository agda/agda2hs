
open import Haskell.Prelude
open import Agda.Builtin.Int using (pos; negsuc)

testInt : Integer → Bool
testInt (pos 10) = True
testInt (negsuc 7) = True
testInt _ = False

{-# COMPILE AGDA2HS testInt #-}

testChar : Char → Bool
testChar 'c' = True
testChar _ = False

{-# COMPILE AGDA2HS testChar #-}
