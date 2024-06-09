{-# LANGUAGE FlexibleInstances #-}


module Test where

import Numeric.Natural (Natural)

import Data.Monoid

data Exp v
  = Plus (Exp v) (Exp v)
  | Lit Natural
  | Var v
  deriving (Show, Eq)

eval :: (a -> Natural) -> Exp a -> Natural
eval env (Plus a b) = eval env a + eval env b
eval env (Lit n) = n
eval env (Var x) = env x

listSum :: [Int] -> Int
listSum [] = 0
listSum (x : xs) = x + sum xs

monoSum :: [Integer] -> Integer
monoSum = sum

polySum :: (Num a) => [a] -> a
polySum = sum

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

ex_word :: Word
ex_word = 0

ex_char :: Char
ex_char = 'a'

char_d :: Char
char_d = toEnum 100

(+++) :: [a] -> [a] -> [a]
[] +++ ys = ys
(x : xs) +++ ys = x : (xs +++ ys)

listMap :: (a -> b) -> [a] -> [b]
listMap f xs = map f xs

mapTest :: [Natural] -> [Natural]
mapTest = map ((5 +))

plus3 :: [Natural] -> [Natural]
plus3 = map (+ 3)

doubleLambda :: Natural -> Natural -> Natural
doubleLambda a b = a + 2 * b

cnst :: a -> b -> a
cnst x _ = x

second :: (b -> c) -> (a, b) -> (a, c)
second f (x, y) = (x, f y)

doubleTake :: Int -> Int -> [a] -> ([a], [a])
doubleTake n m = second (take m) . splitAt n

initLast :: [a] -> ([a], a)
initLast xs = (init xs, last xs)

class MonoidX a where
  memptyX :: a
  mappendX :: a -> a -> a

instance MonoidX Natural where
  memptyX = 0
  mappendX i j = i + j

instance MonoidX (a -> Natural) where
  memptyX _ = memptyX
  mappendX f g x = mappendX (f x) (g x)

instance (MonoidX b) => MonoidX (a -> b) where
  memptyX _ = memptyX
  mappendX f g x = mappendX (f x) (g x)

sumMonX :: (MonoidX a) => [a] -> a
sumMonX xs = foldr mappendX memptyX xs

sumMon :: (Monoid a) => [a] -> a
sumMon xs = foldr (<>) mempty xs

data NatSum = MkSum Natural

instance Semigroup NatSum where
  MkSum a <> MkSum b = MkSum (a + b)

instance Monoid NatSum where
  mempty = MkSum 0

double :: (Monoid a) => a -> a
double x = x <> x

doubleSum :: NatSum -> NatSum
doubleSum = double

hd :: [a] -> a
hd [] = error "hd: empty list"
hd (x : _) = x

five :: Int
five = hd [5, 3]

ex_bool :: Bool
ex_bool = True

ex_if :: Natural
ex_if = if True then 1 else 0

if_over :: Natural
if_over = (if True then id else (+ 1)) 0
