{-# LANGUAGE GADTs #-}
module GadtSyntax
  (Bol(..), Free(..), Color(..))
where

data Bol where
    Tru :: Bol
    Fls :: Bol

data Free f a where
    Return :: a -> Free f a
    Roll :: f (Free f a) -> Free f a

data Color where
    Red :: Color
    Green :: Color
    deriving (Show)

