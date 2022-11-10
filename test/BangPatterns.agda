open import Haskell.Prelude
open import Haskell.Prim using (ℓ)
open import Haskell.Prim.Strict

strictId : Strict a → a
strictId (! x) = x

{-# COMPILE AGDA2HS strictId #-}

myFoldl : (b -> a -> b) -> b -> List a -> b
myFoldl f x0 [] = x0
myFoldl f x0 (x ∷ xs) = myFoldl f (f x0 x) xs

{-# COMPILE AGDA2HS myFoldl #-}

foldl' : (b -> a -> b) -> Strict b -> List a -> b
foldl' f (! x0) [] = x0
foldl' f (! x0) (x ∷ xs) = foldl' f (! f x0 x) xs

{-# COMPILE AGDA2HS foldl' #-}

data LazyMaybe (a : Set ℓ) : Set ℓ where
  LazyNothing : LazyMaybe a
  LazyJust    : a → LazyMaybe a

{-# COMPILE AGDA2HS LazyMaybe #-}

data StrictMaybe (a : Set ℓ) : Set ℓ where
  StrictNothing : StrictMaybe a
  StrictJust    : Strict a → StrictMaybe a

{-# COMPILE AGDA2HS StrictMaybe #-}
