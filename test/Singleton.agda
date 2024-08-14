open import Haskell.Prelude
open import Haskell.Extra.Singleton

test1 : (@0 x : ⊤) → Singleton ⊤ x
test1 x = MkSingl tt

{-# COMPILE AGDA2HS test1 #-}

-- doesn't work because inline functions only reduce because of inline record transformation
test2 : {a b : Set} (f : a → b) {@0 x : a} → Singleton a x → Singleton b (f x)
test2 f {x} sx = fmapSingl f {x} sx

{-# COMPILE AGDA2HS test2 #-}
