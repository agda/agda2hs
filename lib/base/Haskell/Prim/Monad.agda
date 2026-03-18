module Haskell.Prim.Monad where

open import Haskell.Prim
open import Haskell.Prim.Applicative
open import Haskell.Prim.Either
open import Haskell.Prim.Foldable
open import Haskell.Prim.Functor
open import Haskell.Prim.IO
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monoid
open import Haskell.Prim.Tuple


--------------------------------------------------------------------------------
-- Monad

module Do where

  -- ** base
  record Monad (m : Type → Type) : Type₁ where
    field
      _>>=_ : m a → (a → m b) → m b
      overlap ⦃ super ⦄ : Applicative m
      return : a → m a
      _>>_ : m a → (@0 {{ a }} → m b) → m b

  -- ** defaults
  record DefaultMonad (m : Type → Type) : Type₁ where
    field
      _>>=_ : m a → (a → m b) → m b
      overlap ⦃ super ⦄ : Applicative m
    return : a → m a
    return = pure

    _>>_ : m a → (@0 {{ a }} → m b) → m b
    m >> m₁ = m >>= λ x → m₁ {{x}}

  -- ** export
  open Monad ⦃...⦄ public
  {-# COMPILE AGDA2HS Monad existing-class #-}

-- Use `Dont._>>=_` and `Dont._>>_` if you do not want agda2hs to use
-- do-notation.
module Dont where

  open Do using (Monad)

  _>>=_ : ⦃ Monad m ⦄ → m a → (a → m b) → m b
  _>>=_ = Do._>>=_

  _>>_ : ⦃ Monad m ⦄ → m a → (@0 {{ a }} → m b) → m b
  _>>_ = Do._>>_

open Do public

-- ** instances
instance
  open DefaultMonad

  iDefaultMonadList : DefaultMonad List
  iDefaultMonadList ._>>=_ = flip foldMap

  iMonadList : Monad List
  iMonadList = record {DefaultMonad iDefaultMonadList}

  iDefaultMonadMaybe : DefaultMonad Maybe
  iDefaultMonadMaybe ._>>=_ = flip (maybe Nothing)

  iMonadMaybe : Monad Maybe
  iMonadMaybe = record {DefaultMonad iDefaultMonadMaybe}

  iDefaultMonadEither : DefaultMonad (Either a)
  iDefaultMonadEither ._>>=_ = flip (either Left)

  iMonadEither : Monad (Either a)
  iMonadEither = record {DefaultMonad iDefaultMonadEither}

  iDefaultMonadFun : DefaultMonad (λ b → a → b)
  iDefaultMonadFun ._>>=_ = λ f k r → k (f r) r

  iMonadFun : Monad (λ b → a → b)
  iMonadFun = record {DefaultMonad iDefaultMonadFun}

  iDefaultMonadTuple₂ : ⦃ Monoid a ⦄ → DefaultMonad (a ×_)
  iDefaultMonadTuple₂ ._>>=_ = λ (a , x) k → first (a <>_) (k x)

  iMonadTuple₂ : ⦃ Monoid a ⦄ → Monad (a ×_)
  iMonadTuple₂ = record {DefaultMonad iDefaultMonadTuple₂}

  iDefaultMonadTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → DefaultMonad (a × b ×_)
  iDefaultMonadTuple₃ ._>>=_ = λ where
    (a , b , x) k → case k x of λ where
      (a₁ , b₁ , y) → a <> a₁ , b <> b₁ , y

  iMonadTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Monad (a × b ×_)
  iMonadTuple₃ = record {DefaultMonad iDefaultMonadTuple₃}

  iDefaultMonadIO : DefaultMonad IO
  iDefaultMonadIO ._>>=_ = bindIO

  iMonadIO : Monad IO
  iMonadIO = record {DefaultMonad iDefaultMonadIO}
