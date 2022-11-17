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

## Pattern Matching on Datatype Values

Agda
```agda
{-# FOREIGN AGDA2HS {-# LANGUAGE LambdaCase #-} #-}

negate : Bool → Bool
negate True = False
negate False = True

negate' : Bool → Bool
negate' x = case x of λ where
    True → False
    False → True

negate'' : Bool → Bool
negate'' = λ where
    True -> False
    False -> True
```

```hs
{-# LANGUAGE LambdaCase #-}

negate :: Bool -> Bool
negate True = False
negate False = True

negate' :: Bool -> Bool
negate' x = case x of 
    True -> False
    False -> True

negate'' :: Bool -> Bool
negate'' = \case
    True -> False
    False -> True
```

## Partially-Applied Case Pattern Match

```agda
len : List a → Int
len xs = case xs of length
{-# COMPILE AGDA2HS len #-}

applyToFalse : (Bool → a) → a
applyToFalse = case False of_
{-# COMPILE AGDA2HS applyToFalse #-}
```

```hs
len :: List a -> Int 
len xs = length xs

applyToFalse :: (Bool -> a) -> a
applyToFalse = ($ False)
```

## 0-Quantity Parameters

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

Agda:
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

Haskell:
```hs
class Ord a where
    (<) :: a -> a -> Bool
    (>) :: a -> a -> Bool
    {-# MINIMAL (<) | (>) #-}
    (<) = flip (>)
    x > y = y < x
```

## Coppaterns

Agda copatterns are *not* supported by agda2hs in full generality. They *can* be
used to define fields of typeclass instances, for example:

Agda:
```agda
record HasId (a : Set)  : Set where
    field id : a → a
{-# COMPILE AGDA2HS HasId class #-}

instance
    UnitHasId : HasId
    UnitHasId .id x = x
{-# COMPILE AGDA2HS UnitHasId #-}
```

```hs
class HasId a where
    id :: a -> a

instance HasId () where
    id x = x
```

## Partial Application

Agda:
```agda
add1 : Nat → Nat
add1 = 1 +_
{-# COMPILE AGDA2HS add1 #-}
```

Haskell:
```hs
add1 :: Nat -> Nat 
add1 = (1 +)
```

## Mutually Recursive Functions

Agda
```agda
mutual
    even : Nat → Bool
    even Zero = True
    even (Suc n) = odd n

    odd : Nat → Bool
    odd Zero = False
    odd (Suc n) = even n
```

Haskell
```hs
even :: Nat -> Bool
even Zero = True
even (Suc n) = odd n

odd :: Nat -> Bool
odd Zero = False
odd (Suc n) = even n 
```

## Mutually Recursive Datatype and Function

Agda
```agda
mutual

  data Map (k : Set) (a : Set) : Set where
    Bin : (sz : Nat) → (kx : k) → (x : a)
          → (l : Map k a) → (r : Map k a)
          → {{@0 szVal : sz ≡ (size l) + (size r) + 1}}
          → Map k a
    Tip : Map k a
  {-# COMPILE AGDA2HS Map #-}

  size : {k a : Set} → Map k a → Nat
  size Tip = 0
  size (Bin sz _ _ _ _) = sz
  {-# COMPILE AGDA2HS size #-}
```

Haskell
```hs
data Map k a = Bin Natural k a (Map k a) (Map k a)
             | Tip

size :: Map k a -> Natural
size Tip = 0
size (Bin sz _ _ _ _) = sz
```

## Implicit Record Field

Agda
```agda
record ImplicitField (a : Set) : Set where
    field
        aField : a
        @0 {anImplicitField} : a
open ImplicitField public
{-# COMPILE AGDA2HS ImplicitField class #-}
```

Haskell
```hs
class ImplicitField a where
    aField :: a
```

## If-then-else

Agda2Hs implicitly converts the  knows about the Haskell syntax for `ifThenElse`.

Agda
```agda
ifThenElse : Int → String
ifThenElse n = if n >= 10 then "big" else "small"
{-# COMPILE AGDA2HS ifThenElse #-}
```

Haskell
```hs
ifThenElse :: Int -> String
ifThenElse n = if n >= 10 then "big" else "small"
```

## Haskell Language Extensions

Required haskell lengauge extensions will be automatically inferred and enabled.

A Haskell language extension can also be enabled manually as follows:

Agda
```agda
{-# FOREIGN AGDA2HS {-# LANGUAGE LambdaCase #-} #-}
```

Haskell
```hs
{-# LANGUAGE LambdaCase #-}
```