
module Haskell.Prim.Monad where

open import Haskell.Prim
open import Haskell.Prim.Applicative
open import Haskell.Prim.Either
open import Haskell.Prim.Foldable
open import Haskell.Prim.Functor
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monoid
open import Haskell.Prim.String
open import Haskell.Prim.Tuple

--------------------------------------------------
-- Monad

record Monad (m : Set → Set) : Set₁ where
  field
    _>>=_ : m a → (a → m b) → m b
    overlap ⦃ super ⦄ : Applicative m

  return : a → m a
  return = pure

  _>>_ : m a → m b → m b
  m >> m₁ = m >>= λ _ → m₁

  _=<<_ : (a → m b) → m a → m b
  _=<<_ = flip _>>=_

open Monad ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Monad existing-class #-}

mapM₋ : ⦃ Monad m ⦄ → ⦃ Foldable t ⦄ → (a → m b) → t a → m ⊤
mapM₋ f = foldr (λ x k → f x >> k) (pure tt)

sequence₋ : ⦃ Monad m ⦄ → ⦃ Foldable t ⦄ → t (m a) → m ⊤
sequence₋ = foldr _>>_ (pure tt)

instance
  iMonadList : Monad List
  iMonadList ._>>=_ = flip concatMap

  iMonadMaybe : Monad Maybe
  iMonadMaybe ._>>=_ m k = maybe Nothing k m

  iMonadEither : Monad (Either a)
  iMonadEither ._>>=_ m k = either Left k m

  iMonadFun : Monad (λ b → a → b)
  iMonadFun ._>>=_ f k r = k (f r) r

  iMonadTuple₂ : ⦃ Monoid a ⦄ → Monad (a ×_)
  iMonadTuple₂ ._>>=_ (a , x) k = first (a <>_) (k x)

  iMonadTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Monad (a × b ×_)
  iMonadTuple₃ ._>>=_ (a , b , x) k =
    case k x of λ where
      (a₁ , b₁ , y) → a <> a₁ , b <> b₁ , y

  iMonadTuple₄ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ⦃ Monoid c ⦄ →
                 Monad (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))
  iMonadTuple₄ ._>>=_ (a ∷ b ∷ c ∷ x ∷ []) k =
    case k x of λ where
      (a₁ ∷ b₁ ∷ c₁ ∷ y ∷ []) → a <> a₁ ∷ b <> b₁ ∷ c <> c₁ ∷ y ∷ []

record MonadFail (m : Set → Set) : Set₁ where
  field
    fail : String → m a
    overlap ⦃ super ⦄ : Monad m

open MonadFail ⦃ ... ⦄ public

{-# COMPILE AGDA2HS MonadFail existing-class #-}

instance
  MonadFailList : MonadFail List
  MonadFailList .fail _ = []

  MonadFailMaybe : MonadFail Maybe
  MonadFailMaybe .fail _ = Nothing
