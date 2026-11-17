module Issue346
  (D(..), R(..), f, Dummy(..))
where

data D = DC

data R = RC{}

f :: D -> R
f DC = RC

data Dummy = Dum

