module Issue464Class
  (Default(..), TwoMethods(..), Projected(..))
where

class Default a where
    def :: a

class TwoMethods a where
    methodOne :: a
    methodTwo :: a

class Projected a where
    projected :: a
    {-# MINIMAL projected #-}

