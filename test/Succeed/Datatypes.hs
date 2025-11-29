module Datatypes where

data Test = CTest Bool

getTest :: Test -> Bool
getTest (CTest b) = b

putTest :: Bool -> Test -> Test
putTest b (CTest _) = CTest b

