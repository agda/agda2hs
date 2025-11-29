module Issue115 where

class Pointed a where
    it :: a

data A = A1

instance Pointed A where
    it = A1

data Delay a = Later (Delay a)
             | Now a

test :: Delay A
test = Later (Now it)

