module HelloWorld where

type Entry = (Int, [String])

data Tree a = Leaf a
            | Branch a (Tree a) (Tree a)

