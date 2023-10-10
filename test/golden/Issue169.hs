module Issue169 where

newtype Identity a = Identity{runIdentity :: a}

showIdentity :: Show a => Identity a -> String
showIdentity (Identity id) = "Id < " ++ show id ++ " >"

instance (Show a) => Show (Identity a) where
    show = showIdentity

