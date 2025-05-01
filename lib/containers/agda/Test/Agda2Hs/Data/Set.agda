module Test.Agda2Hs.Data.Set where

open import Haskell.Prelude

open import Data.Set using (Set)
import Data.Set as Set

{-----------------------------------------------------------------------------
    Test definitions
    for exercising Data.Set
------------------------------------------------------------------------------}
test0 : Set String
test0 = Set.fromList ("Hello" ∷ "Set" ∷ [])

test1 : Set String
test1 = Set.filter (λ x → length x > 3) test0

test2 : Set String
test2 = Set.singleton "Data"

test3 : Set String
test3 = Set.union test0 (Set.union test1 test2)

test4 : Set String
test4 = Set.intersection test2 test3

testBool0 : Bool
testBool0 = Set.isSubsetOf test2 test4

{-# COMPILE AGDA2HS test0 #-}
{-# COMPILE AGDA2HS test1 #-}
{-# COMPILE AGDA2HS test2 #-}
{-# COMPILE AGDA2HS test3 #-}
{-# COMPILE AGDA2HS test4 #-}
{-# COMPILE AGDA2HS testBool0 #-}
