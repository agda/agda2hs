module Haskell.Law.Monad.List where

open import Haskell.Prim
open import Haskell.Prim.List

open import Haskell.Prim.Monad

open import Haskell.Law.Monad.Def
open import Haskell.Law.List

open import Haskell.Law.Applicative.List

instance
  iLawfulMonadList :  IsLawfulMonad List
  iLawfulMonadList .leftIdentity a k 
    rewrite ++-[] (k a)
    = refl

  iLawfulMonadList .rightIdentity [] = refl
  iLawfulMonadList .rightIdentity (_ ∷ xs)
    rewrite rightIdentity xs
    = refl

  iLawfulMonadList .associativity [] f g = refl
  iLawfulMonadList .associativity (x ∷ xs) f g
    rewrite associativity xs f g
      | concatMap-++-distr (f x) (xs >>= f) g
    = refl  

  iLawfulMonadList .pureIsReturn _ = refl

  iLawfulMonadList .sequence2bind [] _ = refl
  iLawfulMonadList .sequence2bind (f ∷ fs) xs 
    rewrite sequence2bind fs xs
      | map-concatMap f xs
    = refl

  iLawfulMonadList .fmap2bind f [] = refl
  iLawfulMonadList .fmap2bind f (_ ∷ xs)
    rewrite fmap2bind f xs
    = refl

  iLawfulMonadList .rSequence2rBind [] mb = refl
  iLawfulMonadList .rSequence2rBind (x ∷ ma) mb
    rewrite rSequence2rBind ma mb 
      | map-id mb 
    = refl

