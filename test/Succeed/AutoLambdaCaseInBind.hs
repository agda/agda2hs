{-# LANGUAGE LambdaCase #-}
module AutoLambdaCaseInBind
  (lcaseInsideBind)
where

lcaseInsideBind :: Maybe (Maybe a) -> Maybe a
lcaseInsideBind mx
  = do x <- mx
       (\case
            Nothing -> Nothing
            Just _ -> Nothing)
         x

