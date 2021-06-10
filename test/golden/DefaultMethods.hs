module DefaultMethods where

import Haskell.Prim
import Haskell.Prim.Maybe
import Haskell.Prim.Foldable

-- ** Ord

class Ord a where
  (<) :: a -> a -> Bool
  (>) :: a -> a -> Bool

  x < y = y > x
  x > y = y < x

instance Ord Bool where
 false < b = b
 true  < _ = false

type ShowS = String -> String

showString :: String -> ShowS
showString = (++)

showParen : Bool -> ShowS -> ShowS
showParen false s = s
showParen true  s = showString "(" . s . showString ")"

defaultShowList : (a -> ShowS) -> List a -> ShowS
defaultShowList _     []       = showString "[]"
defaultShowList shows (x ∷ xs) = showString "[" ∘ foldl (\ s x → s . showString "," . shows x) (shows x) xs . showString "]"

class Show a where
  show :: a → String
  showPrec :: Int → a → ShowS
  showList :: List a → ShowS

  showPrec _ x s = show x ++ s
  show x = showPrec 0 x ""
  showList = defaultShowList (showPrec 0)

instance Show Bool where
  show True  = "true"
  show False = "false"

  showList [] = showString ""
  showList (true  : bs) = showString "1" . showList bs
  showList (false : bs) = showString "0" . showList bs

instance Show a => Show (Maybe a) where
  showPrec n Nothing  = showString "nothing"
  showPrec n (Just x) = showParen (9 < n) (showString "just " . showPrec 10 x)

instance Show a => Show (List a) where
  showPrec _ = showList
