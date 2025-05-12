```haskell
{-# LANGUAGE LambdaCase #-}
module AutoLambdaCaseInCase where

lcaseInsideCaseOf :: [a] -> Maybe a -> Maybe a
lcaseInsideCaseOf xs
  = case xs of
        [] -> \case
                  Nothing -> Nothing
                  Just _ -> Nothing
        x : _ -> \case
                     Nothing -> Nothing
                     Just _ -> Just x

```
