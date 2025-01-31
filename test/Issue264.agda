open import Haskell.Prim using (Type)

module Issue264 (@0 name : Type) where

data Term : @0 Type → Type where
  Dummy : Term name

{-# COMPILE AGDA2HS Term #-}

reduce : Term name → Term name
reduce v = go v
  where
    go : Term name → Term name
    go v = v

{-# COMPILE AGDA2HS reduce #-}
