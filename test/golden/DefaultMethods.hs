{-# LANGUAGE TypeSynonymInstances #-}

module DefaultMethods where

import Numeric.Natural (Natural)


import Prelude hiding (Show, ShowS, show, showList, showString, showParen, Ord, (<), (>))

class Ord a where
    (<) :: a -> a -> Bool
    (>) :: a -> a -> Bool
    {-# MINIMAL (<) | (>) #-}
    (<) = flip (>)
    x > y = y < x

instance Ord Bool where
    (<) False b = b
    (<) True _ = False

data Bool1 = Mk1 Bool

instance Ord Bool1 where
    (<) (Mk1 False) (Mk1 b) = b
    (<) (Mk1 True) _ = False

data Bool2 = Mk2 Bool

instance Ord Bool2 where
    (<) = (<:)
      where
        (<:) :: Bool2 -> Bool2 -> Bool
        Mk2 False <: Mk2 b = b
        Mk2 True <: _ = False
    (>) = flip (<:)
      where
        (<:) :: Bool2 -> Bool2 -> Bool
        Mk2 False <: Mk2 b = b
        Mk2 True <: _ = False

data Bool3 = Mk3 Bool

instance Ord Bool3 where
    Mk3 False < Mk3 b = b
    Mk3 True < _ = False

data Bool4 = Mk4 Bool

lift4 :: (Bool -> Bool -> a) -> Bool4 -> Bool4 -> a
lift4 f (Mk4 x) (Mk4 y) = f x y

instance Ord Bool4 where
    (<) = lift4 (\ x -> (not x &&))

data Bool5 = Mk5 Bool

instance Ord Bool5 where
    Mk5 False > _ = False
    Mk5 True > Mk5 b = not b

data Bool6 = Mk6 Bool

instance Ord Bool6 where
    (<) = flip (>:)
      where
        (>:) :: Bool6 -> Bool6 -> Bool
        Mk6 False >: _ = False
        Mk6 True >: Mk6 b = not b
    Mk6 False > _ = False
    Mk6 True > Mk6 b = not b

type ShowS = String -> String

showString :: String -> ShowS
showString = (++)

showParen :: Bool -> ShowS -> ShowS
showParen False s = s
showParen True s = showString "(" . s . showString ")"

defaultShowList :: (a -> ShowS) -> [a] -> ShowS
defaultShowList _ [] = showString "[]"
defaultShowList shows (x : xs)
  = showString "[" .
      foldl (\ s x -> s . showString "," . shows x) (shows x) xs .
        showString "]"

class Show a where
    show :: a -> String
    showPrec :: Natural -> a -> ShowS
    showList :: [a] -> ShowS
    {-# MINIMAL showPrec | show #-}
    show x = showPrec 0 x ""
    showList = defaultShowList (showPrec 0)
    showPrec _ x s = show x ++ s

instance Show Bool where
    show True = "true"
    show False = "false"
    showList [] = showString ""
    showList (True : bs) = showString "1" . showList bs
    showList (False : bs) = showString "0" . showList bs

instance (Show a) => Show (Maybe a) where
    showPrec n Nothing = showString "nothing"
    showPrec n (Just x)
      = showParen True (showString "just " . showPrec 10 x)

instance (Show a) => Show ([a]) where
    showPrec _ = showList

