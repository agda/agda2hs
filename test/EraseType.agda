module EraseType where

open import Haskell.Prelude
open import Haskell.Extra.Erase

testErase : Erase Int
testErase = Erased 42

{-# COMPILE AGDA2HS testErase #-}

testMatch : Erase Int → Erase Int
testMatch (Erased x) = Erased (x + 1)

{-# COMPILE AGDA2HS testMatch #-}

testRezz : Rezz (get testErase)
testRezz = rezz 42

{-# COMPILE AGDA2HS testRezz #-}

testRezzErase : Rezz testErase
testRezzErase = rezzErase

{-# COMPILE AGDA2HS testRezzErase #-}

testCong : Rezz (1 + get testErase)
testCong = rezzCong (1 +_) testRezz

{-# COMPILE AGDA2HS testCong #-}

rTail : ∀ {@0 x xs} → Rezz {a = List Int} (x ∷ xs) → Rezz xs
rTail = rezzTail

{-# COMPILE AGDA2HS rTail #-}
