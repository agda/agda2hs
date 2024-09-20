```haskell
module Coinduction where

data Colist a = Nil
              | Cons a (Colist a)

repeater :: a -> Colist a
repeater x = Cons x (repeater x)

```
