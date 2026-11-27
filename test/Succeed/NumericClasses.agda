module NumericClasses where

open import Haskell.Prelude

-- Real

toRat : Int → Rational
toRat = toRational
{-# COMPILE AGDA2HS toRat #-}

-- Integral

quotient : Int → Int → Int
quotient = quot
{-# COMPILE AGDA2HS quotient #-}

remainder : Integer → Integer → Integer
remainder = rem
{-# COMPILE AGDA2HS remainder #-}

euclideanDiv : Integer → Integer → Integer
euclideanDiv = div
{-# COMPILE AGDA2HS euclideanDiv #-}

modulus : Integer → Integer → Integer
modulus = mod
{-# COMPILE AGDA2HS modulus #-}

quotientRemainder : Int → Int → Int × Int
quotientRemainder = quotRem
{-# COMPILE AGDA2HS quotientRemainder #-}

divModulo : Integer → Integer → Integer × Integer
divModulo = divMod
{-# COMPILE AGDA2HS divModulo #-}

makeInteger : Int → Integer
makeInteger = toInteger
{-# COMPILE AGDA2HS makeInteger #-}

-- Fractional

half : Double → Double
half x = x / 2.0
{-# COMPILE AGDA2HS half #-}

invert : Double → Double
invert = recip
{-# COMPILE AGDA2HS invert #-}

fromRat : Rational → Double
fromRat = fromRational
{-# COMPILE AGDA2HS fromRat #-}

-- Floating

constPi : Double
constPi = pi
{-# COMPILE AGDA2HS constPi #-}

naturalLog : Double → Double
naturalLog = log
{-# COMPILE AGDA2HS naturalLog #-}

squareRoot : Double → Double
squareRoot = sqrt
{-# COMPILE AGDA2HS squareRoot #-}

power : Double → Double → Double
power x y = x ** y
{-# COMPILE AGDA2HS power #-}

logBase2 : Double → Double
logBase2 = logBase 2.0
{-# COMPILE AGDA2HS logBase2 #-}

sine : Double → Double
sine = sin
{-# COMPILE AGDA2HS sine #-}

arcTan : Double → Double
arcTan = atan
{-# COMPILE AGDA2HS arcTan #-}

hyperbolicSine : Double → Double
hyperbolicSine = sinh
{-# COMPILE AGDA2HS hyperbolicSine #-}

-- RealFrac

myProperFraction : Double → Integer × Double
myProperFraction = properFraction
{-# COMPILE AGDA2HS myProperFraction #-}

myTruncate : Double → Int
myTruncate = truncate
{-# COMPILE AGDA2HS myTruncate #-}

myRound : Double → Integer
myRound = round
{-# COMPILE AGDA2HS myRound #-}

myCeiling : Double → Int
myCeiling = ceiling
{-# COMPILE AGDA2HS myCeiling #-}

myFloor : Double → Integer
myFloor = floor
{-# COMPILE AGDA2HS myFloor #-}

-- RealFloat

floatRadix' : Double → Integer
floatRadix' = floatRadix
{-# COMPILE AGDA2HS floatRadix' #-}

floatDigits' : Double → Int
floatDigits' = floatDigits
{-# COMPILE AGDA2HS floatDigits' #-}

floatRange' : Double → Int × Int
floatRange' = floatRange
{-# COMPILE AGDA2HS floatRange' #-}

decodeFloat' : Double → Integer × Int
decodeFloat' = decodeFloat
{-# COMPILE AGDA2HS decodeFloat' #-}

encodeFloat' : Integer → Int → Double
encodeFloat' = encodeFloat
{-# COMPILE AGDA2HS encodeFloat' #-}

exponent' : Double → Int
exponent' = exponent
{-# COMPILE AGDA2HS exponent' #-}

significand' : Double → Double
significand' = significand
{-# COMPILE AGDA2HS significand' #-}

scaleFloat' : Int → Double → Double
scaleFloat' = scaleFloat
{-# COMPILE AGDA2HS scaleFloat' #-}

isNaN' : Double → Bool
isNaN' = isNaN
{-# COMPILE AGDA2HS isNaN' #-}

isInfinite' : Double → Bool
isInfinite' = isInfinite
{-# COMPILE AGDA2HS isInfinite' #-}

isDenormalized' : Double → Bool
isDenormalized' = isDenormalized
{-# COMPILE AGDA2HS isDenormalized' #-}

isNegativeZero' : Double → Bool
isNegativeZero' = isNegativeZero
{-# COMPILE AGDA2HS isNegativeZero' #-}

isIEEE' : Double → Bool
isIEEE' = isIEEE
{-# COMPILE AGDA2HS isIEEE' #-}

arcTan2 : Double → Double → Double
arcTan2 = atan2
{-# COMPILE AGDA2HS arcTan2 #-}

-- Rational

someRatio : Rational
someRatio = 1 :% 2
{-# COMPILE AGDA2HS someRatio #-}

mkRatio : Integer → Integer → Ratio Integer
mkRatio x y = x :% y
{-# COMPILE AGDA2HS mkRatio #-}

ratioNumerator : Rational → Integer
ratioNumerator = numerator
{-# COMPILE AGDA2HS ratioNumerator #-}

ratioDenominator : Rational → Integer
ratioDenominator = denominator
{-# COMPILE AGDA2HS ratioDenominator #-}
