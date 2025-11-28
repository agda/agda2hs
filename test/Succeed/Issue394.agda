
open import Haskell.Prelude
open import Haskell.Data.ByteString using (ByteString)

test : ByteString → ByteString → Bool
test x y = x == y

{-# COMPILE AGDA2HS test #-}
