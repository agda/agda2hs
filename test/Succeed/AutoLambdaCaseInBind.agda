open import Haskell.Prelude

lcaseInsideBind : Maybe (Maybe a) → Maybe a
lcaseInsideBind mx = do
  x ← mx
  let go : Maybe a → Maybe a
      go = λ where Nothing  → Nothing
                   (Just _) → Nothing
  go x
{-# COMPILE AGDA2HS lcaseInsideBind #-}
