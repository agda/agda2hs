module Haskell.Data.Maybe where

open import Haskell.Prelude

isJust : Maybe a → Bool
isJust Nothing  = False
isJust (Just _) = True
{-# COMPILE AGDA2HS isJust existing #-}

isNothing : Maybe a → Bool
isNothing Nothing  = True
isNothing (Just _) = False
{-# COMPILE AGDA2HS isNothing existing #-}

fromJust : (x : Maybe a) → @0 {IsJust x} → a
fromJust Nothing  = error "fromJust Nothing"
fromJust (Just x) = x
{-# COMPILE AGDA2HS fromJust existing #-}

fromMaybe : {a : Type} → a → Maybe a → a
fromMaybe d Nothing = d
fromMaybe _ (Just x) = x
{-# COMPILE AGDA2HS fromMaybe existing #-}

listToMaybe : List a → Maybe a
listToMaybe [] = Nothing
listToMaybe (x ∷ _) = Just x
{-# COMPILE AGDA2HS listToMaybe existing #-}

maybeToList : Maybe a → List a
maybeToList Nothing = []
maybeToList (Just x) = x ∷ []
{-# COMPILE AGDA2HS maybeToList existing #-}

mapMaybe : (a → Maybe b) → List a → List b
mapMaybe f [] = []
mapMaybe f (x ∷ xs) = maybe id _∷_ (f x) (mapMaybe f xs)
{-# COMPILE AGDA2HS mapMaybe existing #-}

catMaybes : List (Maybe a) → List a
catMaybes = mapMaybe id
{-# COMPILE AGDA2HS catMaybes existing #-}
