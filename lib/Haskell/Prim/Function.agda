module Haskell.Prim.Function where

open import Haskell.Prim
open import Haskell.Law.Equality

{-|
Pointwise equality on functions.
This says that two functions produce the same
result for all input values.
-}
infix 4 _≗_
_≗_ : ∀ {A B : Set} (f g : A → B) → Set
f ≗ g = ∀ a → f a ≡ g a

