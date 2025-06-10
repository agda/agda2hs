module Test.Agda2Hs.Data.Set where

import Data.Set (Set)
import qualified Data.Set as Set (filter, fromList, intersection, isSubsetOf, singleton, union)

test0 :: Set String
test0 = Set.fromList ["Hello", "Set"]

test1 :: Set String
test1 = Set.filter (\ x -> length x > 3) test0

test2 :: Set String
test2 = Set.singleton "Data"

test3 :: Set String
test3 = Set.union test0 (Set.union test1 test2)

test4 :: Set String
test4 = Set.intersection test2 test3

testBool0 :: Bool
testBool0 = Set.isSubsetOf test2 test4

