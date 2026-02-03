module GadtSyntax where

data Bol where
    Tru :: Bol
    Fls :: Bol

data Free f a where
    Return :: a -> Free f a
    Roll :: f (Free f a) -> Free f a

data Na = Ze
        | Su Na

data Vec a n where
    Nil :: Vec a Ze
    Cons :: a -> Vec a n -> Vec a (Su n)

