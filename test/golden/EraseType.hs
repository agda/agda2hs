module EraseType where

import Haskell.Extra.Erase (rezzErase)

testRezz :: Int
testRezz = 42

testRezzErase :: ()
testRezzErase = rezzErase

