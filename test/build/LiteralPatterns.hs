module LiteralPatterns where

testInt :: Integer -> Bool
testInt 10 = True
testInt (-8) = True
testInt _ = False

testChar :: Char -> Bool
testChar 'c' = True
testChar _ = False

