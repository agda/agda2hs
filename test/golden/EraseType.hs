module EraseType where

testErase :: ()
testErase = ()

testMatch :: () -> ()
testMatch () = ()

testSingleton :: Int
testSingleton = 42

testSingletonErase :: ()
testSingletonErase = ()

testCong :: Int
testCong = 1 + testSingleton

rTail :: [Int] -> [Int]
rTail = \ ys -> tail ys

