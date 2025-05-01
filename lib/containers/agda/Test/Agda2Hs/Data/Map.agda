module Test.Agda2Hs.Data.Map where

open import Haskell.Prelude

open import Data.Map using (Map)
import Data.Map as Map

{-----------------------------------------------------------------------------
    Test definitions
    for exercising Data.Map
------------------------------------------------------------------------------}
test0 : Map Nat String
test0 = Map.fromList ((1 , "Hello") ∷ (2 , "Map") ∷ [])

test1 : Map Nat String
test1 = Map.filter (λ x → length x > 3) test0

test2 : Map Nat String
test2 = Map.singleton 1 "Data"

test3 : Map Nat String
test3 = Map.unionWith _<>_ test0 (Map.unionWith _<>_ test1 test2)

test4 : Map Nat String
test4 = Map.intersectionWith _<>_ test2 test3

testLookup0 : Maybe String
testLookup0 = Map.lookup 1 test4

{-# COMPILE AGDA2HS test0 #-}
{-# COMPILE AGDA2HS test1 #-}
{-# COMPILE AGDA2HS test2 #-}
{-# COMPILE AGDA2HS test3 #-}
{-# COMPILE AGDA2HS test4 #-}
{-# COMPILE AGDA2HS testLookup0 #-}
