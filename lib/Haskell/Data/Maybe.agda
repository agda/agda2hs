module Haskell.Data.Maybe where

open import Haskell.Prelude

isJust : Maybe a → Bool
isJust Nothing  = False
isJust (Just _) = True

isNothing : Maybe a → Bool
isNothing Nothing  = True
isNothing (Just _) = False

fromJust : (x : Maybe a) → @0 {IsJust x} → a
fromJust Nothing  = error "fromJust Nothing"
fromJust (Just x) = x

fromMaybe : {a : Set} → a → Maybe a → a
fromMaybe d Nothing = d
fromMaybe _ (Just x) = x

listToMaybe : List a → Maybe a
listToMaybe [] = Nothing
listToMaybe (x ∷ _) = Just x

maybeToList : Maybe a → List a
maybeToList Nothing = []
maybeToList (Just x) = x ∷ []

mapMaybe : (a → Maybe b) → List a → List b
mapMaybe f [] = []
mapMaybe f (x ∷ xs) = maybe id _∷_ (f x) (mapMaybe f xs)

catMaybes : List (Maybe a) → List a
catMaybes = mapMaybe id
