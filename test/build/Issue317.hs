module Issue317 where

data D = C{unC :: Int}

test :: D -> D
test d = (C . \ r -> unC r) $ d

