module EraseType where

testRezz :: Int
testRezz = 42

testRezzErase :: ()
testRezzErase = ()

testCong :: Int
testCong = 1 + testRezz

rTail :: [Int] -> [Int]
rTail = \ ys -> tail ys

