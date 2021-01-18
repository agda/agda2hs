
module LanguageConstructs where

open import Haskell.Prelude

{-# FOREIGN AGDA2HS {-# LANGUAGE LambdaCase #-} #-}

--------------------------------------------------
-- Lists

oneTwoThree : List Int
oneTwoThree = 1 ∷ 2 ∷ 3 ∷ []
{-# COMPILE AGDA2HS oneTwoThree #-}

exactlyTwo : List a → Maybe (a × a)
exactlyTwo (x ∷ y ∷ []) = Just (x , y)
exactlyTwo _            = Nothing
{-# COMPILE AGDA2HS exactlyTwo #-}


--------------------------------------------------
-- If-then-else

ifThenElse : Int → String
ifThenElse n = if n >= 10 then "big" else "small"
{-# COMPILE AGDA2HS ifThenElse #-}


--------------------------------------------------
-- Case

maybeToList : Maybe a → List a
maybeToList = λ where Nothing  → []
                      (Just x) → x ∷ []
{-# COMPILE AGDA2HS maybeToList #-}

mhead : List a → Maybe a
mhead xs = case xs of λ where
  []      → Nothing
  (x ∷ _) → Just x
{-# COMPILE AGDA2HS mhead #-}

-- Applied to lambda
plus5minus5 : Int → Int
plus5minus5 n = case n + 5 of λ m → m - 5
{-# COMPILE AGDA2HS plus5minus5 #-}

-- Applied to non-lambda
len : List a → Int
len xs = case xs of length
{-# COMPILE AGDA2HS len #-}

-- Underapplied
applyToFalse : (Bool → a) → a
applyToFalse = case false of_
{-# COMPILE AGDA2HS applyToFalse #-}

caseOf : a → (a → b) → b
caseOf = case_of_
{-# COMPILE AGDA2HS caseOf #-}


--------------------------------------------------
-- Enums


enum₁ : List Int
enum₁ = enumFromTo 5 10
{-# COMPILE AGDA2HS enum₁ #-}

enum₂ : List Integer
enum₂ = enumFromThenTo 10 20 100
{-# COMPILE AGDA2HS enum₂ #-}

enum₃ : List Bool
enum₃ = enumFrom false
{-# COMPILE AGDA2HS enum₃ #-}

enum₄ : List Ordering
enum₄ = enumFromThen LT EQ
{-# COMPILE AGDA2HS enum₄ #-}

underappliedEnum : List Int → List (List Int)
underappliedEnum = map (enumFromTo 1)
{-# COMPILE AGDA2HS underappliedEnum #-}
