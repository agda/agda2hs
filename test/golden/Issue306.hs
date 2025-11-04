{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables #-}
module Issue306 where

class Foo a b where
    coe :: a -> b

instance forall a . Foo a a where
    coe x = x

