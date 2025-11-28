module GadtSyntax where

data Bol where
    Tru :: Bol
    Fls :: Bol

data Free f a where
    Return :: a -> Free f a
    Roll :: f (Free f a) -> Free f a

