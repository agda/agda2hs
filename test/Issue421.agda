module Issue421 where

open import Haskell.Prelude

record Identity (a : Type) : Type where
  no-eta-equality
  pattern
  constructor MkIdentity
  field runIdentity : a

open Identity public
{-# COMPILE AGDA2HS Identity newtype #-}

instance
  iDefaultFunctorIdentity : DefaultFunctor Identity
  iDefaultFunctorIdentity .DefaultFunctor.fmap f (MkIdentity x) = MkIdentity (f x)

  iFunctorIdentity : Functor Identity
  iFunctorIdentity = record {DefaultFunctor iDefaultFunctorIdentity}

  iDefaultApplicativeIdentity : DefaultApplicative Identity
  iDefaultApplicativeIdentity .DefaultApplicative.pure = MkIdentity
  iDefaultApplicativeIdentity .DefaultApplicative._<*>_ (MkIdentity f) (MkIdentity x) = MkIdentity (f x)

  iApplicativeIdentity : Applicative Identity
  iApplicativeIdentity = record {DefaultApplicative iDefaultApplicativeIdentity}

{-# COMPILE AGDA2HS iFunctorIdentity #-}
{-# COMPILE AGDA2HS iApplicativeIdentity #-}      -- generates pure and (<*>) multiple times
