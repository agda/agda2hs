module EraseType where

open import Haskell.Prelude
open import Haskell.Extra.Erase

testErase : Erase Int
testErase = Erased 42

{-# COMPILE AGDA2HS testErase #-}

testMatch : Erase Int → Erase Int
testMatch (Erased x) = Erased (x + 1)

{-# COMPILE AGDA2HS testMatch #-}

testSingleton : Singleton (get testErase)
testSingleton = sing 42

{-# COMPILE AGDA2HS testSingleton #-}

testSingletonErase : Singleton testErase
testSingletonErase = singErase

{-# COMPILE AGDA2HS testSingletonErase #-}

testCong : Singleton (1 + get testErase)
testCong = singCong (1 +_) testSingleton

{-# COMPILE AGDA2HS testCong #-}

rTail : ∀ {@0 x xs} → Singleton {a = List Int} (x ∷ xs) → Singleton xs
rTail ys = singTail ys

{-# COMPILE AGDA2HS rTail #-}
