module Usage where

import Definition (CountDown(MkCountdown))

createCountDown :: Int -> Maybe CountDown
createCountDown start
  = if start > 0 then Just (MkCountdown start) else Nothing

