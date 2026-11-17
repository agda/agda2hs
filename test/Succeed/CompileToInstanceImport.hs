module CompileToInstanceImport
  (test)
where

import CompileToInstanceTarget (MyList(Cons, Nil))

test :: Bool
test = eqTest (Cons 1 (Cons 2 Nil)) (Cons 1 (Cons 3 Nil))
  where
    eqTest :: MyList Int -> MyList Int -> Bool
    eqTest x y = x == y

