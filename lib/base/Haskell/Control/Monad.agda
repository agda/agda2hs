module Haskell.Control.Monad where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Int
open import Haskell.Prim.Tuple
open import Haskell.Prim.Applicative
open import Haskell.Prim.Alternative
open import Haskell.Prim.Traversable
open import Haskell.Prim.Foldable
open import Haskell.Data.Foldable using (sequenceA₋; foldlM)
open import Haskell.Data.List using (unzip; zipWith)
open import Haskell.Extra.Erase

open import Haskell.Prim.Functor public
open import Haskell.Prim.Monad public
open import Haskell.Prim.MonadFail public
open import Haskell.Prim.MonadPlus public
open import Haskell.Prim.Traversable public using (mapM; sequence)
open import Haskell.Data.Traversable public using (forM)
open import Haskell.Data.Foldable public using (mapM₋; forM₋; sequence₋; msum)
open import Haskell.Data.Functor public using (void)


variable a1 a2 a3 a4 a5 r : Type

infixr 1 _=<<_ _>=>_ _<=<_
_=<<_ : ⦃ Monad m ⦄ → (a → m b) → m a → m b
_=<<_ = flip _>>=_

_>=>_ : ⦃ Monad m ⦄ → (a → m b) → (b → m c) → a → m c
f >=> g = λ x → f x >>= g

_<=<_ : ⦃ Monad m ⦄ → (b → m c) → (a → m b) → a → m c
_<=<_ = flip _>=>_


join : ⦃ Monad m ⦄ → m (m a) → m a
join x = x >>= id

mfilter : ⦃ MonadPlus m ⦄ → (a → Bool) → m a → m a
mfilter p ma = do
  a ← ma
  if p a then return a else mzero

filterM : ⦃ Applicative m ⦄ → (a → m Bool) → (List a) → m (List a)
filterM p = foldr (λ x → liftA2 (λ b → if b then (x ∷_) else id) (p x)) (pure [])

mapAndUnzipM : ⦃ Applicative m ⦄ → (a → m (b × c)) → (List a) → m (List b × List c)
mapAndUnzipM f xs = fmap unzip (traverse f xs)

zipWithM : ⦃ Applicative m ⦄ → (a → b → m c) → (List a) → (List b) → m (List c)
zipWithM f xs ys = sequenceA (zipWith f xs ys)

zipWithM₋ : ⦃ Applicative m ⦄ → (a → b → m c) → (List a) → (List b) → m ⊤
zipWithM₋ f xs ys = sequenceA₋ (zipWith f xs ys)

foldM : ⦃ Foldable t ⦄ → ⦃ Monad m ⦄ → (b → a → m b) → b → t a → m b
foldM = foldlM

foldM₋ : ⦃ Foldable t ⦄ → ⦃ Monad m ⦄ → (b → a → m b) → b → t a → m ⊤
foldM₋ f a xs  = foldlM f a xs >> return tt

replicateMNat : ⦃ Applicative m ⦄ → Nat → m a → m (List a)
replicateMNat zero    _ = pure []
replicateMNat (suc n) f = liftA2 _∷_ f (replicateMNat n f)

replicateM : ⦃ Applicative m ⦄ → (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → m a → m (List a)
replicateM cnt f = replicateMNat (intToNat cnt) f

replicateMNat₋ : ⦃ Applicative m ⦄ → Nat → m a → m ⊤
replicateMNat₋ zero    _ = pure tt
replicateMNat₋ (suc n) f = f *> replicateMNat₋ n f

replicateM₋ : ⦃ Applicative m ⦄ → (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → m a → m ⊤
replicateM₋ cnt f = replicateMNat₋ (intToNat cnt) f


guard : ⦃ Alternative f ⦄ → (b : Bool) → f (Erase (b ≡ True))
guard True  = pure (Erased refl)
guard False = empty

when : ⦃ Applicative f ⦄ → (b : Bool) → ({@0 p : b ≡ True} → f ⊤) → f ⊤
when True  f = f {refl}
when False _ = pure tt

unless : ⦃ Applicative f ⦄ → (b : Bool) → ({@0 p : b ≡ False} → f ⊤) → f ⊤
unless True  _ = pure tt
unless False f = f {refl}


liftM : ⦃ Monad m ⦄ → (a1 → r) → m a1 → m r
liftM f m1 = do 
  x1 ← m1
  return (f x1)

liftM2 : ⦃ Monad m ⦄ → (a1 → a2 → r) → m a1 → m a2 → m r
liftM2 f m1 m2 = do
  x1 ← m1
  x2 ← m2
  return (f x1 x2)

liftM3 : ⦃ Monad m ⦄ → (a1 → a2 → a3 → r) → m a1 → m a2 → m a3 → m r
liftM3 f m1 m2 m3 = do
  x1 ← m1
  x2 ← m2
  x3 ← m3
  return (f x1 x2 x3)

liftM4 : ⦃ Monad m ⦄ → (a1 -> a2 -> a3 -> a4 -> r) → m a1 → m a2 → m a3 → m a4 → m r
liftM4 f m1 m2 m3 m4 = do
  x1 ← m1
  x2 ← m2
  x3 ← m3
  x4 ← m4
  return (f x1 x2 x3 x4)

liftM5 : ⦃ Monad m ⦄ → (a1 → a2 → a3 → a4 → a5 → r) → m a1 → m a2 → m a3 → m a4 → m a5 → m r
liftM5 f m1 m2 m3 m4 m5 = do
  x1 ← m1
  x2 ← m2
  x3 ← m3
  x4 ← m4
  x5 ← m5
  return (f x1 x2 x3 x4 x5)

ap : ⦃ Monad m ⦄ → m (a → b) → m a → m b
ap m1 m2 = do
  f ← m1
  x ← m2
  return (f x)

infixl 4 _<$!>_
_<$!>_ : ⦃ Monad m ⦄ → (a → b) → m a → m b
_<$!>_ = fmap


-- Omitted for now:
-- - 'forever :: Applicative => f -> f a -> f b'
