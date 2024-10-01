module Issue373 where

open import Haskell.Prelude

{-# FOREIGN AGDA2HS

class MyShow a where
  myshow :: a -> String

#-}

postulate
  MyShow : Set → Set
  myshow : {{ MyShow a }} → a → String

{-# COMPILE AGDA2HS MyShow existing-class #-}

anothershow : {{ MyShow a }} → a → String
anothershow = myshow

{-# COMPILE AGDA2HS anothershow #-}
