# Features

By default, all of the following Agda examples are implicitly prefixed (if
necessary) with the following snippet.

```agda
open import Haskell.Prelude
```

## Data & Type Declarations

### Types

Creating a type synonym using the `type` keyword requires only a simple declaration in Agda.

Agda:
```agda
Entry = Int × List String

{-# COMPILE AGDA2HS Entry #-}
```

Haskell:
```hs
type Entry = (Int, [String])
```

### Datatypes

Standard data type declarations have a simple equivalent in Agda.

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

You can also use polymorphic types in the data declarations.

Agda:
```agda
data Tree (a : Set) : Set where
    Leaf   : a → Tree a
    Branch : a → Tree a → Tree a → Tree a
    
{-# COMPILE AGDA2HS Tree #-}
```

Haskell:
```hs
data Tree a = Leaf a
            | Branch a (Tree a) (Tree a)
```

**UNSUPPORTED: term-indexed datatypes**

### Records

Data definitions with fields are represented by records on the Agda side.

Agda:
```agda
record Citation : Set where
    field
        id     : Int
        author : String
        title  : String
        url    : String
        year   : Int
open Citation public

{-# COMPILE AGDA2HS Citation #-}
```

Haskell:
```hs
data Citation = Citation{id :: Int, author :: String,
                         title :: String, url :: String, year :: Int}
```

### Newtypes

Data declaration using the `newtype` keyword can be created by adding a `newtype` annotation to the compile pragma.

Agda:
```agda
-- data newtype
data Indexed (a : Set) : Set where
    MkIndexed : Int × a → Indexed a

{-# COMPILE AGDA2HS Indexed newtype #-}

-- data newtype with deriving
data Pair (a b : Set) : Set where
    MkPair : a × b → Pair a b

{-# COMPILE AGDA2HS Pair newtype deriving ( Show, Eq ) #-}

-- record newtype
record Identity (a : Set) : Set where
    constructor MkIdentity
    field
        runIdentity : a
open Identity public

{-# COMPILE AGDA2HS Identity newtype #-}

-- record newtype with erased proof
record Equal (a : Set) : Set where
    constructor MkEqual
    field
        pair : a × a
        @0 proof : (fst pair) ≡ (snd pair)
open Equal public

{-# COMPILE AGDA2HS Equal newtype #-}
```

Haskell:
```hs
-- data newtype
newtype Indexed a = MkIndexed (Int, a)

-- data newtype with deriving
newtype Pair a b = MkPair (a, b)
                     deriving (Show, Eq)

-- record newtype
newtype Identity a = MkIdentity{runIdentity :: a}

-- record newtype with erased proof
newtype Equal a = MkEqual{pair :: (a, a)}
```

_Note: Unfortunately, Agda does not allow the constructor name to be the same as the data/record name._

## Pattern Matching on Datatype Values

Agda:
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

## Flow Control

Agda2HS provides native support for the Haskell `if_then_else_` and `case_of_` constructs.

Agda:
```agda
ifThenElse : Int → String
ifThenElse n = if n >= 10 then "big" else "small"
{-# COMPILE AGDA2HS ifThenElse #-}

mhead : List a → Maybe a
mhead xs = case xs of λ where
  []      → Nothing
  (x ∷ _) → Just x
{-# COMPILE AGDA2HS mhead #-}
```

Haskell:
```haskell
ifThenElse :: Int -> String
ifThenElse n = if n >= 10 then "big" else "small"

mhead :: [a] -> Maybe a
mhead xs
  = case xs of
        [] -> Nothing
        x : _ -> Just x
```

> **It is NOT possible to partially apply these two constructs.**
> This means that you must explicitly write `λ x → if x then 2 else 3` instead of `if_then 2 else 3`. (This copies the impossibility of the second implementation in Haskell.)

### Flow Witnesses

While in Haskell such a thing is never necessary, in Agda there are cases when it is useful for a branch to contain a "witness" (proof) of the condition on which it split (i.e. the true branch of `if x < 2 then ... else ...` knows that `x < 2 = True`).

The type signatures of both `if_then_else_` and `case_of_` on the Agda side contain instances of these proofs which can be used to work with e.g. intrinsic verification.

This allows for the following Agda code to type check:
```
data Range : Set where
    MkRange : (low high : Int)
            → {{ @0 h : ((low <= high) ≡ True) }}
            → Range

{-# COMPILE AGDA2HS Range #-}

createRange : Int → Int → Maybe Range
createRange low high = if low <= high then Just (MkRange low high) else Nothing

{-# COMPILE AGDA2HS createRange #-}

createRangeCase : Int → Int → Maybe Range
createRangeCase low high = 
    case low <= high of λ where
        True → Just (MkRange low high)
        False → Nothing

{-# COMPILE AGDA2HS createRangeCase #-}
```

and compile to this simplified Haskell code:
```haskell
data Range = MkRange Int Int

createRange :: Int -> Int -> Maybe Range
createRange low high
  = if low <= high then Just (MkRange low high) else Nothing

createRangeCase :: Int -> Int -> Maybe Range
createRangeCase low high
  = case low <= high of
        True -> Just (MkRange low high)
        False -> Nothing
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

## Type Classes

### Constrained Typeclass Instance

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

### Constrained Typeclass

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

### Default Typeclass Field Implementations

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

### Coppaterns in Type Class Instances

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

### Deriving Type Class Instances

It is also possible to include a standalone `deriving` clause by postulating the instance of a type class.

Agda:
```agda
data Planet : Set where
  Mercury : Planet
  Venus   : Planet
  Earth   : Planet
  Mars    : Planet
  Jupiter : Planet
  Saturn  : Planet
  Uranus  : Planet
  Neptune : Planet
  Pluto   : Planet

{-# COMPILE AGDA2HS Planet #-}

postulate instance iPlanetEq : Eq Planet

{-# COMPILE AGDA2HS iPlanetEq #-}
```

Haskell:
```haskell
data Planet = Mercury
            | Venus
            | Earth
            | Mars
            | Jupiter
            | Saturn
            | Uranus
            | Neptune
            | Pluto

deriving instance Eq Planet
```

This is also possible with more complicated instance definitions, such as in the example below.

Agda:
```agda
data Optional (a : Set) : Set where
  Of    : a → Optional a
  Empty : Optional a

{-# COMPILE AGDA2HS Optional #-}

postulate instance iOptionalEq : ⦃ Eq a ⦄ → Eq (Optional a)

{-# COMPILE AGDA2HS iOptionalEq #-}
```

Haskell:
```haskell
data Optional a = Of a
                | Empty

deriving instance (Eq a) => Eq (Optional a)
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

## Mutual Recursion

### Mutually Recursive Functions

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

### Mutually Recursive Datatype and Function

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

## Haskell Language Extensions

Required haskell langauge extensions will be automatically inferred and enabled.

A Haskell language extension can also be enabled manually as follows:

Agda
```agda
{-# FOREIGN AGDA2HS {-# LANGUAGE LambdaCase #-} #-}
```

Haskell
```hs
{-# LANGUAGE LambdaCase #-}
```

# Imports

Agda supports import statements anywhere in a file, but all generated Haskell imports
will be placed at the top of the file.

Agda
```agda
open import M1 -- imports datatype `A` with constructor `mkA`

a : A
a = mkA
{-# COMPILE AGDA2HS a #-}

open import M2 -- imports datatype `B` with constructor `mkB`

b : B
b = mkB
{-# COMPILE AGDA2HS b #-}
```

Haskell
```hs
import M1 (A(mkA))
import M2 (B(mkB))

a :: A
a = mkA

b :: B
b = bar
```

Note that on the Haskell side all imports are _explicit_,
i.e. indicate the imported identifiers.

Imports can be qualified, but not hidden
(although one can still do this manually using FOREIGN).

Agda
```agda
import MyModule as M -- imports type X and function foo

test : M.X -> M.X
test = M.foo
{-# COMPILE AGDA2HS test #-}
```

Haskell
```hs
import qualified MyModule as M (X, foo)

test :: M.X -> M.X
test = M.foo
```

Other supported features include
- qualifying the Haskell prelude,
- automatically inserting necessary packages for built-in types
- sharing a qualifier across different modules to make a common namespace

Agda
```agda
import Haskell.Prelude as Pre

_+_ : Pre.Nat → Pre.Nat → Pre.Nat
x + y = x
{-# COMPILE AGDA2HS _+_ #-}

test : Pre.Nat
test = 0 Pre.+ 1 + 0
{-# COMPILE AGDA2HS test #-}
```

Haskell
```hs
import Numeric.Natural (Natural)
import qualified Prelude as Pre ((+))

(+) :: Natural -> Natural -> Natural
x + y = x

test :: Natural
test = (Pre.+) 0 (1 + 0)
```

An important difference is that multiple qualifications of the same module
will be absorbed in a single qualifier,
specifically the lexicographically smallest one
based on each character's ASCII value,
independent of the order the imports appear in the source file:

Agda
```agda
import MyModule as C

testC = C.foo
{-# COMPILE AGDA2HS testC #-}

import MyModule as A

testA = A.foo
{-# COMPILE AGDA2HS testA #-}

testB = B.foo
import MyModule as B
{-# COMPILE AGDA2HS testB #-}
```

Haskell
```hs
import qualified MyModule as A (foo)

testC = A.foo
testA = A.foo
testB = A.foo
```



