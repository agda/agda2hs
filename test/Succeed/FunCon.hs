module FunCon
  (D1(..), f1, D2(..), f2)
where

data D1 t = C1 (t Bool)

f1 :: D1 ((->) Int)
f1 = C1 (== 0)

data D2 t = C2 (t Int Int)

f2 :: D2 (->)
f2 = C2 (+ 1)

