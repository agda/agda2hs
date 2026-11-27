module NumericClasses
  (toRat, quotient, remainder, euclideanDiv, modulus, quotientRemainder, divModulo, makeInteger, half, invert, fromRat, constPi, naturalLog, squareRoot, power, logBase2, sine, arcTan, hyperbolicSine, myProperFraction, myTruncate, myRound, myCeiling, myFloor, floatRadix', floatDigits', floatRange', decodeFloat', encodeFloat', exponent', significand', scaleFloat', isNaN', isInfinite', isDenormalized', isNegativeZero', isIEEE', arcTan2, someRatio, mkRatio, ratioNumerator, ratioDenominator)
where

import Data.Ratio (Ratio, Rational, denominator, numerator, (%))

toRat :: Int -> Rational
toRat = toRational

quotient :: Int -> Int -> Int
quotient = quot

remainder :: Integer -> Integer -> Integer
remainder = rem

euclideanDiv :: Integer -> Integer -> Integer
euclideanDiv = div

modulus :: Integer -> Integer -> Integer
modulus = mod

quotientRemainder :: Int -> Int -> (Int, Int)
quotientRemainder = quotRem

divModulo :: Integer -> Integer -> (Integer, Integer)
divModulo = divMod

makeInteger :: Int -> Integer
makeInteger = toInteger

half :: Double -> Double
half x = x / 2.0

invert :: Double -> Double
invert = recip

fromRat :: Rational -> Double
fromRat = fromRational

constPi :: Double
constPi = pi

naturalLog :: Double -> Double
naturalLog = log

squareRoot :: Double -> Double
squareRoot = sqrt

power :: Double -> Double -> Double
power x y = x ** y

logBase2 :: Double -> Double
logBase2 = logBase 2.0

sine :: Double -> Double
sine = sin

arcTan :: Double -> Double
arcTan = atan

hyperbolicSine :: Double -> Double
hyperbolicSine = sinh

myProperFraction :: Double -> (Integer, Double)
myProperFraction = properFraction

myTruncate :: Double -> Int
myTruncate = truncate

myRound :: Double -> Integer
myRound = round

myCeiling :: Double -> Int
myCeiling = ceiling

myFloor :: Double -> Integer
myFloor = floor

floatRadix' :: Double -> Integer
floatRadix' = floatRadix

floatDigits' :: Double -> Int
floatDigits' = floatDigits

floatRange' :: Double -> (Int, Int)
floatRange' = floatRange

decodeFloat' :: Double -> (Integer, Int)
decodeFloat' = decodeFloat

encodeFloat' :: Integer -> Int -> Double
encodeFloat' = encodeFloat

exponent' :: Double -> Int
exponent' = exponent

significand' :: Double -> Double
significand' = significand

scaleFloat' :: Int -> Double -> Double
scaleFloat' = scaleFloat

isNaN' :: Double -> Bool
isNaN' = isNaN

isInfinite' :: Double -> Bool
isInfinite' = isInfinite

isDenormalized' :: Double -> Bool
isDenormalized' = isDenormalized

isNegativeZero' :: Double -> Bool
isNegativeZero' = isNegativeZero

isIEEE' :: Double -> Bool
isIEEE' = isIEEE

arcTan2 :: Double -> Double -> Double
arcTan2 = atan2

someRatio :: Rational
someRatio = 1 % 2

mkRatio :: Integer -> Integer -> Ratio Integer
mkRatio x y = x % y

ratioNumerator :: Rational -> Integer
ratioNumerator = \ r -> numerator r

ratioDenominator :: Rational -> Integer
ratioDenominator = \ r -> denominator r

