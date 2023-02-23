module NewTypePragma where

-- data newtype

newtype Indexed a = MkIndexed (Int, a)

index :: (Int, a) -> Indexed a
index = MkIndexed

-- data newtype with deriving

newtype Pair a b = MkPair (a, b)
                     deriving (Show, Eq)

-- record newtype

newtype Identity a = MkIdentity{runIdentity :: a}

-- record newtype with erased proof

newtype Equal a = MkEqual{pair :: (a, a)}

