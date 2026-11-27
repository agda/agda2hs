module Issue218
  (foo, bar)
where

foo :: Int -> Int
foo n = n

bar :: Int
bar = foo 42

