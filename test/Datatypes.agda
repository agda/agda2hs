
open import Agda.Builtin.Bool

data Test : Set where
  CTest : Bool -> {Bool} -> Test
{-# COMPILE AGDA2HS Test #-}

getTest : Test → Bool
getTest (CTest b) = b
{-# COMPILE AGDA2HS getTest #-}

putTest : Bool → Test → Test
putTest b (CTest _ {b'}) = CTest b {b'}
{-# COMPILE AGDA2HS putTest #-}
