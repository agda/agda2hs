{-# LANGUAGE LambdaCase #-}

module Test where

import Prelude hiding (map, sum, (++))
import Data.Monoid
import Data.Word

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

primFloatPlus :: Double -> Double -> Double
primFloatPlus = (+) :: Double -> Double -> Double

sumF :: [Double] -> Double
sumF [] = 0.0
sumF (x : xs) = primFloatPlus x (sumF xs)

primWord64FromNat :: Integer -> Data.Word.Word64
primWord64FromNat = fromIntegral

primWord64ToNat :: Data.Word.Word64 -> Integer
primWord64ToNat = fromIntegral

ex_word :: Data.Word.Word64
ex_word = primWord64FromNat 0

ex_nat :: Integer
ex_nat = primWord64ToNat ex_word

primCharToNat :: Char -> Integer
primCharToNat = (fromIntegral . fromEnum :: Char -> Integer)

primNatToChar :: Integer -> Char
primNatToChar = (toEnum . fromIntegral :: Integer -> Char)

ex_char :: Char
ex_char = 'a'

toN :: Char -> Integer
toN = primCharToNat

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

