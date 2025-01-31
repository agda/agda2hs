
open import Haskell.Prim using (Bool; Type)

data Test : Type where
  CTest : Bool -> @0 {Bool} -> Test
{-# COMPILE AGDA2HS Test #-}

getTest : Test → Bool
getTest (CTest b) = b
{-# COMPILE AGDA2HS getTest #-}

putTest : Bool → Test → Test
putTest b (CTest _ {b'}) = CTest b {b'}
{-# COMPILE AGDA2HS putTest #-}
