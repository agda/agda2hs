
open import Haskell.Prelude

-- Example from http://learnyouahaskell.com/a-fistful-of-monads#getting-our-feet-wet-with-maybe

Birds = Int
Pole = Birds × Birds

{-# COMPILE AGDA2HS Birds #-}
{-# COMPILE AGDA2HS Pole #-}


landLeft : Birds → Pole → Maybe Pole
landLeft n (left , right) =
  if abs ((left + n) - right) < 4
  then Just (left + n , right)
  else Nothing

{-# COMPILE AGDA2HS landLeft #-}

landRight : Birds → Pole → Maybe Pole
landRight n (left , right) =
  if abs (left - (right + n)) < 4
  then Just (left , right + n)
  else Nothing

{-# COMPILE AGDA2HS landRight #-}

routine : Maybe Pole
routine = do
    start ← return (0 , 0)
    first ← landLeft 2 start
    second ← landRight 2 first
    landLeft 1 second

{-# COMPILE AGDA2HS routine #-}

routineWithoutDo : Maybe Pole
routineWithoutDo =
    return (0 , 0) Dont.>>= λ start →
    landLeft 2 start Dont.>>= λ first →
    landRight 2 first Dont.>>= λ second →
    landLeft 1 second

{-# COMPILE AGDA2HS routineWithoutDo #-}

swapPolesMaybe : Maybe Pole → Maybe Pole
swapPolesMaybe x = do
  (one , two) ← x
  pure (two , one)

{-# COMPILE AGDA2HS swapPolesMaybe #-}
