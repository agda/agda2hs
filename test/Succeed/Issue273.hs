module Issue273 where

test :: (Int, Int) -> Int
test = ((\ r -> snd r) $)

mySnd :: (Int, Int) -> Int
mySnd x = snd x

test2 :: (Int, Int) -> Int
test2 = (mySnd $)

test3 :: (Int, Int) -> Int
test3 = \ x -> snd x

test4 :: (Int, Int) -> Int
test4 = mySnd

test5 :: (Int, Int) -> Int -> Int
test5 = \ x _ -> (\ r -> snd r) $ x

test6 :: Int -> Int
test6 = ((1 + 1) `subtract`)

test7 :: Int -> Int
test7 = (+ (1 - 1))

