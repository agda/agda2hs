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

Unfortunately, Agda does not allow the constructor name to be the same as the data/record name.
However, it _is_ possible to achieve this with Agda2HS if you do not explicitly add a constructor name to a record definition (this requires the use of `record { ... }` syntax on the Agda side):

```agda
record Duo (a : Set) : Set where
    field
        duo : a × a
open Duo public

{-# COMPILE AGDA2HS Duo newtype #-}

createDuo : a → a → Duo a
createDuo a b = record { duo = a , b }

{-# COMPILE AGDA2HS createDuo #-}
```

```hs
newtype Duo a = Duo{duo :: (a, a)}

createDuo :: a -> a -> Duo a
createDuo a b = Duo (a, b)
```

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
```agda
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

## Explicit type singatures

Haskell's `::` syntax for explicit type signatures can be achieved using the `the` function in Haskell.Prim.

Agda:
```agda
five : Nat
five = the (Nat -> Nat) id 5
{-# COMPILE AGDA2HS five #-}
```

Haskell:
```hs
five :: Natural
five = (id :: Natural -> Natural) 5
```

(0-Quantity)=
## 0-Quantity Parameters

Parameters can be annotated with a _quantity_ of either `0` or `ω` (the default quantity is `ω` if no quantity is explicitly annotated). Such parameters are irrelevant to evaluation, so they are irrelevant to the compiled Haskell program, and so agda2hs erases them.

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

To construct an instance of a type class, you can simply do the following:

Agda:
```agda
record Circle : Set where
    constructor MkCircle
    field
        radius : Int
open Circle public

{-# COMPILE AGDA2HS Circle newtype #-}

instance
  iCircleEq : Eq Circle
  iCircleEq ._==_ (MkCircle r1) (MkCircle r2) = r1 == r2

{-# COMPILE AGDA2HS iCircleEq #-}
```

Haskell:
```hs
newtype Circle = MkCircle{radius :: Int}

instance Eq Circle where
    MkCircle r1 == MkCircle r2 = r1 == r2
```

In some cases (especially when writing proofs), it might be necessary to use the properties (laws) that a type class instance should uphold.
In this case, you can also implement the `IsLawful` instance for the data type and use it's (erased) properties.

Agda:
```agda
record Equal (a : Set) : Set where
    constructor MkEqual
    field
        pair : a × a
        @0 proof : fst pair ≡ snd pair
open Equal public

{-# COMPILE AGDA2HS Equal newtype #-}

constructEqual : ⦃ iEqA : Eq a ⦄ → @0 ⦃ IsLawfulEq a ⦄ → (c : a) → (d : a) → Maybe (Equal a)
constructEqual a b = 
  if a == b then
    (λ ⦃ h ⦄ → Just (MkEqual (a , b) (equality a b h)))
  else Nothing

{-# COMPILE AGDA2HS constructEqual #-}

instance
  iLawfulCircleEq : IsLawfulEq Circle
  iLawfulCircleEq .isEquality (MkCircle r1) (MkCircle r2)
    with r1 == r2 in eq
  ... | True  = ofY (cong MkCircle (equality r1 r2 eq))
  ... | False = ofN λ ceq → (nequality r1 r2 eq) (cong radius ceq)

constructEqualCircle : (c : Circle) → (d : Circle) → Maybe (Equal Circle)
constructEqualCircle c d = constructEqual c d

{-# COMPILE AGDA2HS constructEqualCircle #-}
```

Haskell:
```hs
newtype Equal a = MkEqual{pair :: (a, a)}

constructEqual :: Eq a => a -> a -> Maybe (Equal a)
constructEqual a b
  = if a == b then Just (MkEqual (a, b)) else Nothing

constructEqualCircle :: Circle -> Circle -> Maybe (Equal Circle)
constructEqualCircle c d = constructEqual c d
```

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

### Copatterns in Type Class Instances

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

If the derived instance is not needed on the Agda side and needs to only be generated in Haskell, the deriving clause can simply be added to the compilation pragma (this also works with the `newtype` pragma):

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

{-# COMPILE AGDA2HS Planet deriving ( Read ) #-}
```

Haskell:
```hs
data Planet = Mercury
            | Venus
            | Earth
            | Mars
            | Jupiter
            | Saturn
            | Uranus
            | Neptune
            | Pluto
                deriving (Read)
```

It is also possible to include a standalone `deriving` clause which makes the instance available on the Agda side by
* adding the `derive` pragma to an implemented instance,
* or postulating the instance.

Agda:
```agda
instance
  iPlanetEq : Eq Planet
  iPlanetEq ._==_ Mercury Mercury = True
  iPlanetEq ._==_ Venus   Venus   = True
  iPlanetEq ._==_ Earth   Earth   = True
  iPlanetEq ._==_ Mars    Mars    = True
  iPlanetEq ._==_ Jupiter Jupiter = True
  iPlanetEq ._==_ Saturn  Saturn  = True
  iPlanetEq ._==_ Uranus  Uranus  = True
  iPlanetEq ._==_ Neptune Neptune = True
  iPlanetEq ._==_ Pluto   Pluto   = True
  iPlanetEq ._==_ _       _       = False

{-# COMPILE AGDA2HS iPlanetEq derive #-}

postulate instance iPlanetOrd : Ord Planet

{-# COMPILE AGDA2HS iPlanetOrd #-}
```

Haskell:
```hs
deriving instance Eq Planet

deriving instance Ord Planet
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

Or even with deriving strategies, by specifying them within the derive pragma (Agda2HS will also automatically set the language flags):

Agda:
```agda
postulate instance iPlanetShow : Show Planet

{-# COMPILE AGDA2HS iPlanetShow derive stock #-}

record Clazz (a : Set) : Set where
  field
    foo : a → Int
    bar : a → Bool

open Clazz ⦃...⦄ public

{-# COMPILE AGDA2HS Clazz class #-}

postulate instance iPlanetClazz : Clazz Planet

{-# COMPILE AGDA2HS iPlanetClazz derive anyclass #-}

data Duo (a b : Set) : Set where
  MkDuo : (a × b) → Duo a b

{-# COMPILE AGDA2HS Duo newtype #-}

postulate instance iDuoEq : ⦃ Eq a ⦄ → ⦃ Eq b ⦄ → Eq (Duo a b)

{-# COMPILE AGDA2HS iDuoEq derive newtype #-}
```

Haskell:
```haskell
{-# LANGUAGE StandaloneDeriving, DerivingStrategies,
  DeriveAnyClass, GeneralizedNewtypeDeriving #-}

deriving stock instance Show Planet

class Clazz a where
    foo :: a -> Int
    bar :: a -> Bool

deriving anyclass instance Clazz Planet

newtype Duo a b = MkDuo (a, b)

deriving newtype instance (Eq a, Eq b) => Eq (Duo a b)
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

Required haskell language extensions will be automatically inferred and enabled.

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

# Rewrite rules and Prelude imports

## Rewrite rules

User-defined rewrite rules can be defined through a YAML configuration
file. It is enabled with the `--config` option.

This feature is particularly useful if you have a project depending on a large
library which is not agda2hs-compatible (e.g the standard library).
In this case, you might not want to rewrite the entire library, but may
still rely on it for proofs.

User-defined rewrite rules can help translating the library functions to ones available
in the Haskell Prelude, or even to those written by yourself. In the latter
case, place a Haskell file (e.g. `Base.hs`) next to your `.agda` files that
contains your custom definitions and provide this custom module in the
`importing` clauses of the config file.

To an extent, this compromises the mathematically proven correctness of your project.
But if you trust that your (or Prelude's) functions are equivalent to the original ones,
this might not be a problem.
You can also prove the equivalence of the two definitions to be safe.

For example, let's suppose we want to compile the following file:

```agda
open import Data.Nat as ℕ
open import Data.Integer as ℤ
open import Data.Rational.Unnormalised as ℚ

double : ℚᵘ → ℚᵘ
double p = (+ 2 / 1) ℚ.* p
{-# COMPILE AGDA2HS double #-}

-- this will use denominator-1 and suc from BaseExample.hs
twoDenoms : ℚᵘ → ℕ
twoDenoms p = 2 ℕ.* (ℕ.suc (ℚᵘ.denominator-1 p))
{-# COMPILE AGDA2HS twoDenoms #-}
```

By default, the output would be this:

```hs
module Example where

import Data.Rational.Unnormalised.Base (ℚᵘ(denominator-1), (/))
import qualified Data.Rational.Unnormalised.Base as ℚ ((*))
import Numeric.Natural (Natural)
import qualified Prelude as ℕ ((*))

double :: ℚᵘ -> ℚᵘ
double p = (ℚ.*) (pos 2 / 1) p

twoDenoms :: ℚᵘ -> Natural
twoDenoms p = (ℕ.*) 2 (suc (denominator-1 p))
```

Here, agda2hs doesn't know where to find these definitions; so it simply leaves them as they are.

Run this again with the following config file:

```yaml
rewrites:
  - from: "Agda.Builtin.Nat.Nat.suc"
    to: "suc"
    importing: "BaseExample"
  - from: "Agda.Builtin.Nat._*_"
    to: "_*_"
    importing: "Prelude"
  - from: "Agda.Builtin.Int.Int.pos"
    to: "toInteger"
    importing: "Prelude"
  - from: "Data.Rational.Unnormalised.Base.ℚᵘ"
    to: "Rational"
    importing: "Data.Ratio"
  - from: "Data.Rational.Unnormalised.Base._*_"
    to: "_*_"
    importing: "Prelude"
  - from: "Data.Rational.Unnormalised.Base._/_"
    to: "_%_"
    importing: "Data.Ratio"
  - from: "Data.Rational.Unnormalised.Base.ℚᵘ.denominator-1"
    to: "denominatorMinus1"
    importing: "BaseExample"
```

The names are a bit difficult to find. It helps if you run agda2hs with a verbosity level of 26 and check the logs (specifically the parts beginning with `compiling name`).

The output is now this:

```hs
module Example where

import BaseExample (denominatorMinus1, suc)
import Data.Ratio (Rational, (%))
import Numeric.Natural (Natural)
import Prelude (toInteger, (*))

double :: Rational -> Rational
double p = toInteger 2 % 1 * p

twoDenoms :: Rational -> Natural
twoDenoms p = 2 * suc (denominatorMinus1 p)
```

With a manually written `BaseExample.hs` file like this, GHCi accepts it:

```hs
module BaseExample where

import Numeric.Natural
import Data.Ratio

suc :: Natural -> Natural
suc = (1 +)

denominatorMinus1 :: Rational -> Natural
denominatorMinus1 = fromIntegral . denominator
```

See also `rewrite-rules-example.yaml` in the root of the repository.

## Handling of Prelude

By default, agda2hs handles Prelude like other modules: it collects all the
identifiers it finds we use from Prelude, and adds them to Prelude's import
list.

A different behaviour can be specified in a YAML configuration file.
The format is the following:

```yaml
# First, we specify how to handle Prelude.
prelude:
  implicit: true
  hiding:           # if implicit is true
    - seq

  #using:           # if implicit is false
  #  - +
  #  - Num

# Then the rules themselves.
rewrites:

  # The rational type.
  - from: "Data.Rational.Unnormalised.Base.ℚᵘ"
    to: "Rational"
    importing: "Data.Ratio"

  # ...
```

If `implicit` is `true`, then everything gets imported from Prelude, except for those that are specified in the `hiding` list. This can cause clashes if you reuse names from Prelude, hence the opportunity for a `hiding` list. If there is no such list, then everything gets imported.

If `implicit` is `false`, Prelude gets imported explicitly, and only those identifiers that are specified in the `using` list. If there is no such list, agda2hs reverts to the default behaviour (it tries to collect imports by itself).

## Known issues

- Rewrite rules only work for things you do use, not for those that you only define. This causes a problem with class instances: if you choose the default behaviour, then write an instance of the Num class and define signum but do not use it, it will not get into Prelude's import list, and so GHC will complain.
- You cannot change to a version with arguments of different modality without getting useless code. So if you rewrite a function to a version which has some of its parameters erased, the parameters remain there; probably because rewriting happens only after compiling the type signature.

# Emacs mode

Since there is a full Agda typechecker in the `agda2hs` binary,
you can readily use the Emacs mode of a pre-existing Agda installation (make sure it is the same version as the one `agda2hs` depends on) by changing the binary that `agda-mode` uses (Lisp variable `agda2-program-name`) to (the path to) `agda2hs` binary.

With `C-c C-x C-c`, you will now be able call the `agda2hs` backend from inside Emacs; all the other built-in backends still remain available.

## Known issues

- Now, the output can only be written next to the `.agda` files;
  there is no option to collect these under a separate directory.
- The `--config` option is not yet supported in Emacs mode.

