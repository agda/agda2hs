
module LanguageConstructs where

open import Haskell.Prelude

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
