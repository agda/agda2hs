{-# LANGUAGE RankNTypes #-}
module CompileToAlpha
  (targetList, targetLam, targetCase, targetDo, targetRankN)
where

import CompileToAlphaDataTarget (Target)
import CompileToAlphaInstanceTarget (MyList)
import Numeric.Natural (Natural)

targetList :: [a] -> [a]
targetList xs = go xs
  where
    go :: [a] -> [a]
    go [] = []
    go (x : xs) = x : go xs

targetLam :: [Natural] -> [Natural]
targetLam xs = map (\ k -> k + 1) xs

targetCase :: Maybe Natural -> Natural
targetCase m
  = case m of
        Just x -> x
        Nothing -> 0

targetDo :: Maybe Natural -> Maybe Natural
targetDo m
  = do x <- m
       pure (succ x)

targetRankN :: (forall a . a -> a) -> Natural
targetRankN f = f 0

