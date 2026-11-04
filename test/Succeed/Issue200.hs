{-# LANGUAGE LambdaCase #-}
module Issue200
  (Void(..), test)
where

data Void

test :: Maybe Void -> Maybe Void
test
  = \case
        Nothing -> Nothing

