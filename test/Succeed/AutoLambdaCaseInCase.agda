open import Haskell.Prelude

lcaseInsideCaseOf : List a → (Maybe a → Maybe a)
lcaseInsideCaseOf xs = case xs of λ where
  []      → λ where Nothing → Nothing
                    (Just _) → Nothing
  (x ∷ _) → λ where Nothing → Nothing
                    (Just _) → Just x
{-# COMPILE AGDA2HS lcaseInsideCaseOf #-}
