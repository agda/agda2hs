```haskell
module Sections where

import Numeric.Natural (Natural)

test₁ :: Natural -> Natural
test₁ = (5 +)

test₂ :: Natural -> Natural
test₂ = (+ 5)

test₃ :: Natural -> Natural
test₃ = (5 +)

test₄ :: Natural -> Natural
test₄ = \ x -> x + 5

test₅ :: Natural -> Natural
test₅ = (5 +)

```
