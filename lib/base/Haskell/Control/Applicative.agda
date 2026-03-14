module Haskell.Control.Applicative where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Applicative public
open import Haskell.Prim.Alternative public
open import Haskell.Data.Functor public using (_<$>_)
open import Haskell.Data.Foldable public using (asum)


infixl 4 _<**>_
_<**>_ : ⦃ Applicative f ⦄ → f a → f (a → b) → f b
_<**>_ = liftA2 (λ a f → f a)

liftA : ⦃ Applicative f ⦄ → (a → b) → f a → f b
liftA f a = pure f <*> a

liftA3 : ⦃ Applicative f ⦄ → (a → b → c → d) → f a → f b → f c → f d
liftA3 f a b c = liftA2 f a b <*> c

optional : ⦃ Alternative f ⦄ → f a → f (Maybe a)
optional v = Just <$> v <|> pure Nothing

-- Omitted for now:
-- - 'newtype Const a (b :: k) = Const { getConst :: a }'
-- - 'newtype WrappedMonad (m :: Type -> Type) a = WrapMonad { unwrapMonad :: m a }'
-- - 'newtype WrappedArrow (a :: Type -> Type -> Type) b c = WrapArrow { unwrapArrow :: a b c }'
-- - 'newtype ZipList a = ZipList { getZipList :: [a] }'