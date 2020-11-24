{-# LANGUAGE LambdaCase #-}

module Test where

import Data.Word (Word64)
import Numeric.Natural (Natural)

import Prelude hiding (sum)
import Data.Monoid
-- import Data.Word

-- import Data.Word (Word64)
import qualified Data.Word as Word64

data Exp v = Plus (Exp v) (Exp v)
           | Int Natural
           | Var v

eval :: (a -> Natural) -> Exp a -> Natural
eval env (Plus a b) = eval env a + eval env b
eval env (Int n) = n
eval env (Var x) = env x

sum :: [Natural] -> Natural
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

(+++) :: [a] -> [a] -> [a]
[] +++ ys = ys
(x : xs) +++ ys = x : xs +++ ys

listMap :: (a -> b) -> [a] -> [b]
listMap f [] = []
listMap f (x : xs) = f x : listMap f xs

mapTest :: [Natural] -> [Natural]
mapTest = map (id . (5 +))

plus3 :: [Natural] -> [Natural]
plus3 = map (\ n -> n + 3)

doubleLambda :: Natural -> Natural -> Natural
doubleLambda = \ a b -> a + 2 * b

class MonoidX a where
        memptyX :: a
        mappendX :: a -> a -> a

sumMonX :: MonoidX a => [a] -> a
sumMonX [] = memptyX
sumMonX (x : xs) = mappendX x (sumMonX xs)

sumMon :: Monoid a => [a] -> a
sumMon [] = mempty
sumMon (x : xs) = x <> sumMon xs

ex_bool :: Bool
ex_bool = True

ex_if :: Natural
ex_if = if True then 1 else 0

if_over :: Natural
if_over = (if True then \ x -> x else \ x -> x + 1) 0

if_partial₁ :: [Natural] -> [Natural]
if_partial₁ = map (\ f -> if True then 1 else f)

if_partial₂ :: [Natural] -> [Natural -> Natural]
if_partial₂ = map (\ t f -> if True then t else f)

if_partial₃ :: [Bool] -> [Natural -> Natural -> Natural]
if_partial₃ = map (\ b t f -> if b then t else f)

if_partial₄ :: [Bool] -> [Natural -> Natural]
if_partial₄ = map (\ section f -> if section then 1 else f)

if_partial₅ :: Bool -> Natural -> [Natural] -> [Natural]
if_partial₅ b f = map (\ f₁ -> if b then f else f₁)

