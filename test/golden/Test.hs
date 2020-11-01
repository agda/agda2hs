{-# LANGUAGE LambdaCase #-}

module Test where

import Data.Word (Word64)
import Prelude hiding (map, sum, (++))
import Data.Monoid
-- import Data.Word

-- import Data.Word (Word64)
import qualified Data.Word as Word64

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

ex_float :: Double
ex_float = 0.0

ex_word :: Word64
ex_word = fromInteger 0

ex_char :: Char
ex_char = 'a'

char_d :: Char
char_d = toEnum 100

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

ex_bool :: Bool
ex_bool = True

ex_if :: Integer
ex_if = if True then 1 else 0

if_over :: Integer
if_over = (if True then \ x -> x else \ x -> x + 1) 0

if_partial₁ :: [Integer] -> [Integer]
if_partial₁ = map (\ f -> if True then 1 else f)

if_partial₂ :: [Integer] -> [Integer -> Integer]
if_partial₂ = map (\ t f -> if True then t else f)

if_partial₃ :: [Bool] -> [Integer -> Integer -> Integer]
if_partial₃ = map (\ b t f -> if b then t else f)

if_partial₄ :: [Bool] -> [Integer -> Integer]
if_partial₄ = map (\ section f -> if section then 1 else f)

if_partial₅ :: Bool -> Integer -> [Integer] -> [Integer]
if_partial₅ b f = map (\ f₁ -> if b then f else f₁)

