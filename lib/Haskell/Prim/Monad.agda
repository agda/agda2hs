
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
open import Haskell.Prim.String
open import Haskell.Prim.Tuple

--------------------------------------------------
-- Monad

module Do where

  -- ** base
  record Monad (m : Set → Set) : Set₁ where
    field
      _>>=_ : m a → (a → m b) → m b
      overlap ⦃ super ⦄ : Applicative m
      return : a → m a
      _>>_ : m a → (@0 {{ a }} → m b) → m b
  -- ** defaults
  record DefaultMonad (m : Set → Set) : Set₁ where
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

_=<<_ : {{Monad m}} → (a → m b) → m a → m b
_=<<_ = flip _>>=_

mapM₋ : ⦃ Monad m ⦄ → ⦃ Foldable t ⦄ → (a → m b) → t a → m ⊤
mapM₋ f = foldr (λ x k → f x >> k) (pure tt)

sequence₋ : ⦃ Monad m ⦄ → ⦃ Foldable t ⦄ → t (m a) → m ⊤
sequence₋ = foldr (λ mx my → mx >> my) (pure tt)

-- ** instances
private
  mkMonad : DefaultMonad t → Monad t
  mkMonad x = record {DefaultMonad x}

  infix 0 bind=_
  bind=_ : ⦃ Applicative m ⦄ → (∀ {a b} → m a → (a → m b) → m b) → Monad m
  bind= x = record {DefaultMonad (record {_>>=_ = x})}
instance
  iDefaultMonadList : DefaultMonad List
  iDefaultMonadList .DefaultMonad._>>=_ = flip concatMap

  iMonadList : Monad List
  iMonadList = record {DefaultMonad iDefaultMonadList}

  iDefaultMonadMaybe : DefaultMonad Maybe
  iDefaultMonadMaybe .DefaultMonad._>>=_ = flip (maybe Nothing)

  iMonadMaybe : Monad Maybe
  iMonadMaybe = record {DefaultMonad iDefaultMonadMaybe}

  iDefaultMonadEither : DefaultMonad (Either a)
  iDefaultMonadEither .DefaultMonad._>>=_ = flip (either Left)

  iMonadEither : Monad (Either a)
  iMonadEither = record {DefaultMonad iDefaultMonadEither}

  iDefaultMonadFun : DefaultMonad (λ b → a → b)
  iDefaultMonadFun .DefaultMonad._>>=_ = λ f k r → k (f r) r

  iMonadFun : Monad (λ b → a → b)
  iMonadFun = record {DefaultMonad iDefaultMonadFun}

  iDefaultMonadTuple₂ : ⦃ Monoid a ⦄ → DefaultMonad (a ×_)
  iDefaultMonadTuple₂ .DefaultMonad._>>=_ = λ (a , x) k → first (a <>_) (k x)

  iMonadTuple₂ : ⦃ Monoid a ⦄ → Monad (a ×_)
  iMonadTuple₂ = record {DefaultMonad iDefaultMonadTuple₂}

  iDefaultMonadTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → DefaultMonad (a × b ×_)
  iDefaultMonadTuple₃ .DefaultMonad._>>=_ = λ where
    (a , b , x) k → case k x of λ where
      (a₁ , b₁ , y) → a <> a₁ , b <> b₁ , y

  iMonadTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Monad (a × b ×_)
  iMonadTuple₃ = record {DefaultMonad iDefaultMonadTuple₃}

instance postulate iMonadIO : Monad IO

record MonadFail (m : Set → Set) : Set₁ where
  field
    fail : String → m a
    overlap ⦃ super ⦄ : Monad m

open MonadFail ⦃...⦄ public

{-# COMPILE AGDA2HS MonadFail existing-class #-}

instance
  MonadFailList : MonadFail List
  MonadFailList .fail _ = []

  MonadFailMaybe : MonadFail Maybe
  MonadFailMaybe .fail _ = Nothing
