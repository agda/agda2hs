{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables #-}
module Issue306
  (Foo(..))
where

class Foo a b where
    coe :: a -> b

instance forall a . Foo a a where
    coe x = x

