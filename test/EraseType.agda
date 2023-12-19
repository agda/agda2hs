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
