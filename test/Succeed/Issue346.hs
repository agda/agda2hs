module Issue346
  (D(..), R(..), f)
where

data D = DC

data R = RC{}

f :: D -> R
f DC = RC

