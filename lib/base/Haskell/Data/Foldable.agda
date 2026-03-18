module Haskell.Data.Foldable where

open import Haskell.Prim
open import Haskell.Prim.Monad
open import Haskell.Prim.Applicative
open import Haskell.Prim.Alternative
open import Haskell.Prim.MonadPlus
open import Haskell.Prim.Monoid
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe

open import Haskell.Prim.Foldable public


foldrM : ⦃ Foldable t ⦄ → ⦃ Monad m ⦄ → (a → b → m b) → b → t a → m b
foldrM f z0 xs = foldl (λ k x z → f x z >>= k) return xs z0

foldlM : ⦃ Foldable t ⦄ → ⦃ Monad m ⦄ → (b → a → m b) → b → t a → m b
foldlM f z0 xs = foldr (λ x k z → f z x >>= k) return xs z0

traverse₋ : ⦃ Foldable t ⦄ → ⦃ Applicative f ⦄ → (a → f b) → t a → f ⊤
traverse₋ f = foldr (λ x m → f x *> m) (pure tt)

for₋ : ⦃ Foldable t ⦄ → ⦃ Applicative f ⦄ → t a → (a → f b) → f ⊤
for₋ = flip traverse₋

mapM₋ : ⦃ Foldable t ⦄ → ⦃ Monad m ⦄ → (a → m b) → t a → m ⊤
mapM₋ f = foldr (λ x m → f x >> m) (pure tt)

forM₋ : ⦃ Foldable t ⦄ → ⦃ Monad m ⦄ → t a → (a → m b) → m ⊤
forM₋ = flip mapM₋

sequenceA₋ : ⦃ Foldable t ⦄ → ⦃ Applicative f ⦄ → t (f a) → f ⊤
sequenceA₋ = foldr (λ mx my → mx *> my) (pure tt)

sequence₋ : ⦃ Foldable t ⦄ → ⦃ Monad m ⦄ → t (m a) → m ⊤
sequence₋ = foldr (λ mx my → mx >> my) (pure tt)

asum : ⦃ Foldable t ⦄ → ⦃ Alternative f ⦄ → t (f a) → f a
asum = foldr _<|>_ empty

msum : ⦃ Foldable t ⦄ → ⦃ MonadPlus m ⦄ → t (m a) → m a
msum = asum

concat : ⦃ Foldable t ⦄ → t (List a) → List a
concat = fold

concatMap : ⦃ Foldable t ⦄ → (a → List b) → t a → List b
concatMap = foldMap

any : ⦃ Foldable t ⦄ → (a → Bool) → t a → Bool
any ⦃ i ⦄ = foldMap ⦃ i ⦄ ⦃ MonoidDisj ⦄

all : ⦃ Foldable t ⦄ → (a → Bool) → t a → Bool
all ⦃ i ⦄ = foldMap ⦃ i ⦄ ⦃ MonoidConj ⦄

and : ⦃ Foldable t ⦄ → t Bool → Bool
and = all id

or : ⦃ Foldable t ⦄ → t Bool → Bool
or = any id

maximumBy : ⦃ _ : Foldable t ⦄ → (a → a → Ordering) → (s : t a) → @0 ⦃ NonEmpty (toList s) ⦄ → a
maximumBy {a = a} cmp = foldr1 max'
  where
    max' : a → a → a
    max' x y with cmp x y
    ...         | GT = x
    ...         | _  = y

minimumBy : ⦃ _ : Foldable t ⦄ → (a → a → Ordering) → (s : t a) → @0 ⦃ NonEmpty (toList s) ⦄ → a
minimumBy {a = a} cmp = foldr1 min'
  where
    min' : a → a → a
    min' x y with cmp x y
    ...         | GT = y
    ...         | _  = x

notElem : ⦃ Foldable t ⦄ → ⦃ Eq a ⦄ → a → t a → Bool
notElem x t = not (elem x t)

find : ⦃ Foldable t ⦄ → (a → Bool) → t a → Maybe a
find ⦃ i ⦄ p = foldMap ⦃ i ⦄ ⦃ MonoidFirst ⦄ (λ x → if p x then Just x else Nothing)
