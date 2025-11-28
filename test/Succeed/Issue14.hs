module Issue14 where

import Numeric.Natural (Natural)

constid :: a -> b -> b
constid x = \ x -> x

sectionTest₁ :: Natural -> Natural -> Natural
sectionTest₁ n = (+ n)

sectionTest₂ :: Natural -> Natural -> Natural
sectionTest₂ section = (+ section)

