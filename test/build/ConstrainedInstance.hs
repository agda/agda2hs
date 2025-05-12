module ConstrainedInstance where

data D a = C a

instance (Eq a) => Eq (D a) where
    C x == C y = x == y

