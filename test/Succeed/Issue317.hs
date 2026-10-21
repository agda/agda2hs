module Issue317
  (D(..), test)
where

data D = C{unC :: Int}

test :: D -> D
test d = (C . \ r -> unC r) $ d

