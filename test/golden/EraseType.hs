module EraseType where

testErase :: ()
testErase = ()

testMatch :: () -> ()
testMatch () = ()

testRezz :: Int
testRezz = 42

testRezzErase :: ()
testRezzErase = ()

testCong :: Int
testCong = 1 + testRezz

rTail :: [Int] -> [Int]
rTail = \ ys -> tail ys

