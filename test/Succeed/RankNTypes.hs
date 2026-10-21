{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Haskell98 #-}

module RankNTypes where

data MyBool = MyTrue
            | MyFalse

rank2ForallUse :: (forall a . a -> a) -> MyBool
rank2ForallUse f = f MyTrue

rank2Module :: (forall a . a -> a) -> MyBool
rank2Module f = f MyTrue

