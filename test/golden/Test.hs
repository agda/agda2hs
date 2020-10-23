{-# LANGUAGE LambdaCase #-}

module Test where

import Prelude hiding (map, sum, (++))
import Data.Monoid

data Exp v = Plus (Exp v) (Exp v)
           | Int Integer
           | Var v

eval :: (a -> Integer) -> Exp a -> Integer
eval env (Plus a b) = eval env a + eval env b
eval env (Int n) = n
eval env (Var x) = env x

sum :: [Integer] -> Integer
sum [] = 0
sum (x : xs) = x + sum xs

-- comment
-- another comment
bla :: Int -> Int
bla n = n * 4

{- multi
   line
   comment
-}

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x : xs) ++ ys = x : xs ++ ys

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x : xs) = f x : map f xs

plus3 :: [Integer] -> [Integer]
plus3 = map (\ n -> n + 3)

doubleLambda :: Integer -> Integer -> Integer
doubleLambda = \ a b -> a + 2 * b

