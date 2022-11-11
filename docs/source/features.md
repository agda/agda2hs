⦃→

# Features

By default, all of the following Agda examples are implicitly prefixed (if
necessary) with the following snippet.
```agda
open import Haskell.Prelude
```

## Datatypes

Agda:
```agda
data Nat : Set where
    Zero : Nat 
    Suc : Nat → Nat
{-# COMPILE AGDA2HS Nat #-}
```

Haskell:
```hs
data Nat = Zero | Suc Nat
```

**UNSUPPORTED: term-indexed datatypes**

## 0-Qualtity Parameters

Parameters can be annotated with a _quantiy_ of either `0` or `ω` (the default quantity is `ω` if not quantity is explicitly annotated). Such parameters are irrelevant to evaluation, so they are irrelevant to the compiled Haskell program, and so agda2hs erases them.

Agda:
```agda
data GhostInt : Set where
    MakeGhostInt : @0 Int → GhostInt

-- fails
fromGhostInt : GhostInt -> Int
fromGhostInt (MakeGhostInt i) = i

-- passes
addGhostInts : GhostInt -> GhostInt -> GhostInt
addGhostInts (MakeGhostInt i) (MakeGhostInt j) = MakeGhostInt (i + j)
```

Haskell:
```hs
data GhostInt = MakeGhostInt

addGhostInts :: GhostInt -> GhostInt -> GhostInt
addGhostInts MakeGhostInt MakeGhostInt = MakeGhostInt
```

## Coinduction

Agda:
```agda
data Stream (a : Set) (@0 i : Size) : Set where
    Nil : Stream a i
    Cons : a → Thunk (Stream a) i → Stream a i
{-# COMPILE AGDA2HS Stream #-}

repeat {a} {i} : a → Stream a i
repeat x = Cons x λ where .force → repeat x
{-# COMPILE AGDA2HS repeat #-}
```

Haskell:
```hs
data Stream a = Nil | Cons a (Stream a)

repeat :: a -> Stream a
repeat x = Cons x (repeat x)
```

## Constrained Typeclass Instance

Agda:
```agda
record Class1 (a : Set) : Set where
    field
        field1 : a
{-# COMPILE AGDA2HS Class1 class #-}

record Class2 (a : Set) : Set where
    field
        field2 : a
{-# COMPILE AGDA2HS Class2 class #-}

class1-implies-class2 (a : Set) : Class1 a → Class2 a
class1-implies-class2 _ class1 = record { field2 = class1.field1 }
{-# COMPILE AGDA2HS class1-implies-class2 #-}
```

Haskell:
```hs
class Class1 a where
    field1 :: a

class Class2 where
    field2 :: a

instance Class1 a => Class2 a where
    field2 = field1
```

## Constrained Typeclass

Agda:
```agda
record Class1 (a : Set) : Set where
    field
        field1 : a
{-# COMPILE AGDA2HS Class1 class #-}

record Class2 (a : Set) : Set where
    field
        overlap ⦃ super ⦄ : ClassA b
        field2 : a
{-# COMPILE AGDA2HS Class2 class #-}
```

Haskell:
```hs
class Class1 a where
    field1 :: a 

class Class1 a => Class2 a where
    field2 :: a 
```

## Default Typeclass Field Implementations

```agda
record Ord (a : Set) : Set where
  field
    _<_ _>_ : a → a → Bool

record Ord₁ (a : Set) : Set where
  field
    _<_ : a → a → Bool

  _>_ : a → a → Bool
  x > y = y < x

record Ord₂ (a : Set) : Set where
  field
    _>_ : a → a → Bool

  _<_ : a → a → Bool
  _<_ = flip _>_

open Ord ⦃ ... ⦄

{-# COMPILE AGDA2HS Ord class Ord₁ Ord₂ #-}

instance 
    Ord₁-Bool : Ord₁ Bool
    Ord₁-Bool .Ord₁._<_ False b = b
    Ord₁-Bool .Ord₁._<_ True _ = False

instance
   Ord₂-Bool : Ord₂ Bool
   Ord₂-Bool .Ord₂.
```

```hs
class Ord a where
    (<) :: a -> a -> Bool
    (>) :: a -> a -> Bool
    {-# MINIMAL (<) | (>) #-}
    (<) = flip (>)
    x > y = y < x
```