module NonClassInstance
  (foo, bar)
where

foo :: Bool -> Bool -> Bool
foo _ b = not b

bar :: Bool -> Bool
bar b = foo b b

