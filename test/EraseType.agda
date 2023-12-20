module EraseType where

open import Haskell.Prelude
open import Haskell.Extra.Erase

testErase : Erase Int
testErase = Erased 42

{-# COMPILE AGDA2hs testErase #-}

testRezz : Rezz Int (get testErase)
testRezz = rezz 42

{-# COMPILE AGDA2HS testRezz #-}

testRezzErase : Rezz (Erase Int) testErase
testRezzErase = rezzErase

{-# COMPILE AGDA2HS testRezzErase #-}

testCong : Rezz Int (1 + get testErase)
testCong = rezzCong (1 +_) testRezz

{-# COMPILE AGDA2HS testCong #-}

rTail : ∀ {@0 x xs} → Rezz (List Int) (x ∷ xs) → Rezz (List Int) xs
rTail = rezzTail

{-# COMPILE AGDA2HS rTail #-}
