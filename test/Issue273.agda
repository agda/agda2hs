module Issue273 where

open import Haskell.Prelude

test : Int × Int → Int
test = λ x → snd $ x
{-# COMPILE AGDA2HS test #-}

mySnd : Int × Int → Int
mySnd x = snd x
{-# COMPILE AGDA2HS mySnd #-}

test2 : Int × Int → Int
test2 = λ x → mySnd $ x
{-# COMPILE AGDA2HS test2 #-}

test3 : Int × Int → Int
test3 = λ x → snd x
{-# COMPILE AGDA2HS test3 #-}

test4 : Int × Int → Int
test4 = λ x → mySnd x
{-# COMPILE AGDA2HS test4 #-}

test5 : Int × Int → Int → Int
test5 = λ x _ → snd $ x
{-# COMPILE AGDA2HS test5 #-}

test6 : Int → Int
test6 = _- (1 + 1)
{-# COMPILE AGDA2HS test6 #-}

test7 : Int → Int
test7 = _+ (1 - 1)
{-# COMPILE AGDA2HS test7 #-}
