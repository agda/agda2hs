module HeightMirror where

data Tree a = Tip
            | Bin a (Tree a) (Tree a)

mirror :: Tree a -> Tree a
mirror Tip = Tip
mirror (Bin x lt rt) = Bin x (mirror rt) (mirror lt)

