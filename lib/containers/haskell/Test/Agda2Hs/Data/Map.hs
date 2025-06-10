module Test.Agda2Hs.Data.Map where

import Data.Map (Map)
import qualified Data.Map as Map (filter, fromList, intersectionWith, lookup, singleton, unionWith)
import Numeric.Natural (Natural)

test0 :: Map Natural String
test0 = Map.fromList [(1, "Hello"), (2, "Map")]

test1 :: Map Natural String
test1 = Map.filter (\ x -> length x > 3) test0

test2 :: Map Natural String
test2 = Map.singleton 1 "Data"

test3 :: Map Natural String
test3 = Map.unionWith (<>) test0 (Map.unionWith (<>) test1 test2)

test4 :: Map Natural String
test4 = Map.intersectionWith (<>) test2 test3

testLookup0 :: Maybe String
testLookup0 = Map.lookup 1 test4

