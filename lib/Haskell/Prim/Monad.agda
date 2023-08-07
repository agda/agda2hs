
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
      _=<<_ : (a → m b) → m a → m b
  -- ** defaults
  record DefaultMonad (m : Set → Set) : Set₁ where
    field
      _>>=_ : m a → (a → m b) → m b
      overlap ⦃ super ⦄ : Applicative m
    return : a → m a
    return = pure

    _>>_ : m a → (@0 {{ a }} → m b) → m b
    m >> m₁ = m >>= λ x → m₁ {{x}}

    _=<<_ : (a → m b) → m a → m b
    _=<<_ = flip _>>=_
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
  iMonadList : Monad List
  iMonadList = bind= flip concatMap

  iMonadMaybe : Monad Maybe
  iMonadMaybe = bind= flip (maybe Nothing)

  iMonadEither : Monad (Either a)
  iMonadEither = bind= flip (either Left)

  iMonadFun : Monad (λ b → a → b)
  iMonadFun = bind= λ f k r → k (f r) r

  iMonadTuple₂ : ⦃ Monoid a ⦄ → Monad (a ×_)
  iMonadTuple₂ = bind= λ (a , x) k → first (a <>_) (k x)

  iMonadTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Monad (a × b ×_)
  iMonadTuple₃ = bind= λ (a , b , x) k →
    case k x of λ where
      (a₁ , b₁ , y) → a <> a₁ , b <> b₁ , y

  iMonadTuple₄ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ⦃ Monoid c ⦄ →
                 Monad (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))
  iMonadTuple₄ = bind= λ (a ; b ; c ; x ; tt) k →
    case k x of λ where
      (a₁ ; b₁ ; c₁ ; y ; tt) → a <> a₁ ; b <> b₁ ; c <> c₁ ; y ; tt

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
