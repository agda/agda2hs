module Issue421 where

newtype Identity a = MkIdentity{runIdentity :: a}

instance Functor Identity where
    fmap f (MkIdentity x) = MkIdentity (f x)

instance Applicative Identity where
    pure = MkIdentity
    MkIdentity f <*> MkIdentity x = MkIdentity (f x)

