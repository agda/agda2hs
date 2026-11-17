{-# LANGUAGE MultiParamTypeClasses #-}
module RelevantDotPattern5
  (Cast(..))
where

class Cast a b where
    runCast :: a -> b

instance (a ~ b) => Cast a b where
    runCast x = x

