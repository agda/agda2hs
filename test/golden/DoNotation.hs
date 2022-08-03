module DoNotation where

type Birds = Int

type Pole = (Birds, Birds)

landLeft :: Birds -> Pole -> Maybe Pole
landLeft n (left, right)
  = if abs (left + n - right) < 4 then Just (left + n, right) else
      Nothing

landRight :: Birds -> Pole -> Maybe Pole
landRight n (left, right)
  = if abs (left - (right + n)) < 4 then Just (left, right + n) else
      Nothing

routine :: Maybe Pole
routine
  = do start <- return (0, 0)
       first <- landLeft 2 start
       landRight 2 first >>= landLeft 1

