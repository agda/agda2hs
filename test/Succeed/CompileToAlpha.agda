module CompileToAlpha where

open import Haskell.Prelude
open import CompileToAlphaDataTarget
open import CompileToAlphaInstanceTarget

-- Every definition below is paired with a target that only differs in the names
-- of local variables and/or auxiliary `where` definitions. The `to` pragmas
-- must accept them, so this module should not produce any warnings.

-- Pattern variables and a local `where` definition.
targetList : List a → List a
targetList xs = go xs
  where
    go : List a → List a
    go []       = []
    go (x ∷ xs) = x ∷ go xs

sourceList : List b → List b
sourceList ys = helper ys
  where
    helper : List b → List b
    helper []       = []
    helper (y ∷ ys) = y ∷ helper ys

{-# COMPILE AGDA2HS targetList #-}
{-# COMPILE AGDA2HS sourceList to targetList #-}

-- Lambda bound variables.
targetLam : List Nat → List Nat
targetLam xs = map (λ k → k + 1) xs

sourceLam : List Nat → List Nat
sourceLam ys = map (λ j → j + 1) ys

{-# COMPILE AGDA2HS targetLam #-}
{-# COMPILE AGDA2HS sourceLam to targetLam #-}

-- Pattern variables in a case alternative.
targetCase : Maybe Nat → Nat
targetCase m = case m of λ where
  (Just x) → x
  Nothing  → 0

sourceCase : Maybe Nat → Nat
sourceCase n = case n of λ where
  (Just y) → y
  Nothing  → 0

{-# COMPILE AGDA2HS targetCase #-}
{-# COMPILE AGDA2HS sourceCase to targetCase #-}

-- A variable bound by a `do` generator.
targetDo : Maybe Nat → Maybe Nat
targetDo m = do
  x ← m
  pure (suc x)

sourceDo : Maybe Nat → Maybe Nat
sourceDo n = do
  y ← n
  pure (suc y)

{-# COMPILE AGDA2HS targetDo #-}
{-# COMPILE AGDA2HS sourceDo to targetDo #-}

-- An explicitly quantified type variable in an argument type.
targetRankN : (∀ {a} → a → a) → Nat
targetRankN f = f 0

sourceRankN : (∀ {b} → b → b) → Nat
sourceRankN g = g 0

{-# COMPILE AGDA2HS targetRankN #-}
{-# COMPILE AGDA2HS sourceRankN to targetRankN #-}

-- The compiled instance differs from the target only in the name of its local
-- `where` helper and its pattern variables.
data Vec (a : Set) : Set where
  Nil  : Vec a
  Cons : a → Vec a → Vec a

{-# COMPILE AGDA2HS Vec to MyList #-}

instance
  iEqVec : {{Eq a}} → Eq (Vec a)
  iEqVec {a} ._==_ = eqVec
    where
      eqVec : Vec a → Vec a → Bool
      eqVec Nil Nil = True
      eqVec (Cons x xs) (Cons y ys) = x == y && eqVec xs ys
      eqVec _ _ = False

{-# COMPILE AGDA2HS iEqVec to iEqMyList #-}

record Wrap (a : Type) : Type where
  constructor wrap
  field unwrap : Maybe a
open Wrap public
{-# COMPILE AGDA2HS Wrap unboxed #-}

-- The source instance is an identity clause, so it is consistent with the
-- target as long as the instance heads match up to alpha-equivalence. The head
-- uses a different type variable name than the target instance `iEqMaybe`.
instance
  iEqWrap : {{Eq c}} → Eq (Wrap c)
  iEqWrap ._==_ x y = unwrap x == unwrap y

{-# COMPILE AGDA2HS iEqWrap to iEqMaybe #-}

-- The constructor argument types differ only in the name of the type variable
-- bound by the rank-N type, so the datatype must be accepted as a compile-to
-- target up to alpha-equivalence.
data Source (a : Set) : Set₁ where
  MkTarget : (∀ {y : Set} → y → y) → a → Source a

{-# COMPILE AGDA2HS Source to Target #-}
