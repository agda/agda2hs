open import Haskell.Prelude hiding (pure; _<*>_)
open import Haskell.Extra.Singleton as Singleton

test1 : (@0 x : ⊤) → Singleton ⊤ x
test1 x = MkSingl tt

{-# COMPILE AGDA2HS test1 #-}

-- doesn't work because inline functions only reduce because of inline record transformation
test2 : {a b : Set} (f : a → b) {@0 x : a} → Singleton a x → Singleton b (f x)
test2 f {x} sx = fmapSingl f {x} sx

{-# COMPILE AGDA2HS test2 #-}

test3 : {@0 x y : Nat} → Singleton Nat x → Singleton Nat y → Singleton Nat (x + y)
test3 x y = (| x + y |)
  where open Singleton.Idiom

{-# COMPILE AGDA2HS test3 #-}
