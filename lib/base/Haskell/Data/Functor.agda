module Haskell.Data.Functor where

open import Haskell.Prim
open import Haskell.Prim.Tuple

open import Haskell.Prim.Functor public
  renaming (module Instances to FunctorInstances)


infixl 4 _$>_
_$>_ : ⦃ Functor f ⦄ → f a → (@0 ⦃ a ⦄ → b) → f b
_$>_ = flip _<$_

infixl 4 _<$>_
_<$>_ : ⦃ Functor f ⦄ → (a → b) → f a → f b
_<$>_ = fmap

infixl 1 _<&>_
_<&>_ : ⦃ Functor f ⦄ → f a → (a → b) → f b
m <&> f = fmap f m

unzip : ⦃ Functor f ⦄ → f (a × b) -> (f a × f b)
unzip xs = fst <$> xs , snd <$> xs

void : ⦃ Functor f ⦄ → f a → f ⊤
void = tt <$_
