{-# OPTIONS --no-auto-inline #-}

module Haskell.Prelude where

open import Haskell.Prim                public
  using (Type;
         Bool; True; False; Char; Integer;
         List; []; _∷_; Nat; zero; suc; ⊤; tt;
         TypeError; ⊥; iNumberNat;
         IsTrue; IsFalse; NonEmpty;
         All; allNil; allCons;
         Any; anyHere; anyThere;
         id; _∘_; _$_; flip; const;
         if_then_else_; case_of_;
         Number; fromNat; Negative; fromNeg;
         IsString; fromString;
         _≡_; refl;
         a; b; c; d; e; f; m; s; t)
open import Haskell.Prim.Absurd         public
open import Haskell.Prim.Bool           public
open import Haskell.Prim.Bounded        public
  renaming (module Instances to BoundedInstances)
open import Haskell.Prim.Char           public
open import Haskell.Prim.Double         public
open import Haskell.Prim.Either         public
open import Haskell.Prim.Enum           public
  renaming (module Instances to EnumInstances)
open import Haskell.Prim.Int            public
open import Haskell.Prim.Integer        public
open import Haskell.Prim.IO             public
  hiding (returnIO; bindIO; failIO; mplusIO)
open import Haskell.Prim.Maybe          public
open import Haskell.Prim.Tuple          public hiding (first; second; _***_)
open import Haskell.Prim.Word           public
open import Haskell.Prim.Eq             public
  renaming (module Instances to EqInstances)
open import Haskell.Prim.Ord            public
  renaming (module Instances to OrdInstances)
open import Haskell.Prim.Num            public
  renaming (module Instances to NumInstances)
open import Haskell.Prim.Show           public
  renaming (module Instances to ShowInstances)
open import Haskell.Prim.Semigroup      public
  renaming (module Instances to SemigroupInstances)
open import Haskell.Prim.Monoid         public
  renaming (module Instances to MonoidInstances)

-- Explicitly reexport definitions from Haskell.Data.Functor (update these
-- to use Agda's builtin reexport mechanism as soon as issue #126 is fixed):
import Haskell.Data.Functor

module Functor = Haskell.Data.Functor.Functor
module DefaultFunctor = Haskell.Data.Functor.DefaultFunctor
module FunctorInstances = Haskell.Data.Functor.FunctorInstances

open Functor ⦃ ... ⦄ public

Functor : (f : Type → Type) → Type₁
Functor = Haskell.Data.Functor.Functor

DefaultFunctor : (f : Type → Type) → Type₁
DefaultFunctor = Haskell.Data.Functor.DefaultFunctor

infixl 4 _<$>_
_<$>_ : ⦃ Haskell.Data.Functor.Functor f ⦄ → (a → b) → f a → f b
_<$>_ = Haskell.Data.Functor._<$>_

-- Explicitly reexport definitions from Haskell.Control.Applicative (update these
-- to use Agda's builtin reexport mechanism as soon as issue #126 is fixed):
import Haskell.Control.Applicative

module Applicative = Haskell.Control.Applicative.Applicative
module ApplicativeFrom<*> = Haskell.Control.Applicative.ApplicativeFrom<*>
module ApplicativeFromLiftA2 = Haskell.Control.Applicative.ApplicativeFromLiftA2
module ApplicativeInstances = Haskell.Control.Applicative.ApplicativeInstances

open Applicative ⦃ ... ⦄ public

Applicative : (f : Type → Type) → Type₁
Applicative = Haskell.Control.Applicative.Applicative

ApplicativeFrom<*> : (f : Type → Type) → Type₁
ApplicativeFrom<*> = Haskell.Control.Applicative.ApplicativeFrom<*>

ApplicativeFromLiftA2 : (f : Type → Type) → Type₁
ApplicativeFromLiftA2 = Haskell.Control.Applicative.ApplicativeFromLiftA2

-- Explicitly reexport definitions from Haskell.Control.Monad (update these
-- to use Agda's builtin reexport mechanism as soon as issue #126 is fixed):
import Haskell.Control.Monad

module Monad = Haskell.Control.Monad.Monad
module DefaultMonad = Haskell.Control.Monad.DefaultMonad
module MonadInstances = Haskell.Control.Monad.MonadInstances
module Dont = Haskell.Control.Monad.Dont

module MonadFail = Haskell.Control.Monad.MonadFail
module MonadFailInstances = Haskell.Control.Monad.MonadFailInstances

open Monad ⦃ ... ⦄ public
open MonadFail ⦃ ... ⦄ public

Monad : (m : Type → Type) → Type₁
Monad = Haskell.Control.Monad.Monad

DefaultMonad : (m : Type → Type) → Type₁
DefaultMonad = Haskell.Control.Monad.DefaultMonad

MonadFail : (m : Type → Type) → Type₁
MonadFail = Haskell.Control.Monad.MonadFail

infixr 1 _=<<_
_=<<_ : ⦃ Monad m ⦄ → (a → m b) → m a → m b
_=<<_ = Haskell.Control.Monad._=<<_

-- Explicitly reexport definitions from Haskell.Data.Foldable (update these
-- to use Agda's builtin reexport mechanism as soon as issue #126 is fixed):
import Haskell.Data.Foldable

module Foldable = Haskell.Data.Foldable.Foldable
  hiding (fold; foldMap'; foldr'; toList; null; length)
module DefaultFoldable = Haskell.Data.Foldable.DefaultFoldable
module FoldableInstances = Haskell.Data.Foldable.FoldableInstances

open Foldable ⦃ ... ⦄ public

Foldable : (t : Type → Type) → Type₁
Foldable = Haskell.Data.Foldable.Foldable

DefaultFoldable : (t : Type → Type) → Type₁
DefaultFoldable = Haskell.Data.Foldable.DefaultFoldable

mapM₋ : ⦃ Foldable t ⦄ → ⦃ Monad m ⦄ → (a → m b) → t a → m ⊤
mapM₋ = Haskell.Data.Foldable.mapM₋

sequence₋ : ⦃ Foldable t ⦄ → ⦃ Monad m ⦄ → t (m a) → m ⊤
sequence₋ = Haskell.Data.Foldable.sequence₋

-- Explicitly reexport definitions from Haskell.Data.Traversable (update these
-- to use Agda's builtin reexport mechanism as soon as issue #126 is fixed):
import Haskell.Data.Traversable

module Traversable = Haskell.Data.Traversable.Traversable
module DefaultTraversable = Haskell.Data.Traversable.DefaultTraversable
module TraversableInstances = Haskell.Data.Traversable.TraversableInstances

open Traversable ⦃ ... ⦄ public

Traversable : (t : Type → Type) → Type₁
Traversable = Haskell.Data.Traversable.Traversable

-- Explicitly reexport definitions from Haskell.Data.String (update these
-- to use Agda's builtin reexport mechanism as soon as issue #126 is fixed):
import Haskell.Data.String

String : Type
String = Haskell.Data.String.String

instance iIsStringString : IsString String
iIsStringString = Haskell.Data.String.iIsStringString

lines : String → List String
lines = Haskell.Data.String.lines

words : String → List String
words = Haskell.Data.String.words

unlines : List String → String
unlines = Haskell.Data.String.unlines

unwords : List String → String
unwords = Haskell.Data.String.unwords

-- Explicitly reexport definitions from Haskell.Data.List (update these
-- to use Agda's builtin reexport mechanism as soon as issue #126 is fixed):
import Haskell.Data.List

infixr 5 _++_
_++_ : List a → List a → List a
_++_ = Haskell.Data.List._++_

map : (a → b) → List a → List b
map = Haskell.Data.List.map

reverse : List a → List a
reverse = Haskell.Data.List.reverse

lengthNat : List a → Nat
lengthNat = Haskell.Data.List.lengthNat

length : ⦃ Foldable t ⦄ → t a → Int
length = Haskell.Data.List.length

head : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → a
head = Haskell.Data.List.head

last : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → a
last = Haskell.Data.List.last

tail : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → List a
tail = Haskell.Data.List.tail

init : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → List a
init = Haskell.Data.List.init

infixl 9 _!!ᴺ_
_!!ᴺ_ : (xs : List a) (n : Nat) → @0 ⦃ IsTrue (n < lengthNat xs) ⦄ → a
_!!ᴺ_ = Haskell.Data.List._!!ᴺ_

infixl 9 _!!_
_!!_ : (xs : List a) (n : Int)
     → ⦃ @0 _ : IsNonNegativeInt n ⦄
     → ⦃ @0 _  : IsTrue (intToNat n < lengthNat xs) ⦄ → a
_!!_ = Haskell.Data.List._!!_

splitAtNat : (n : Nat) → List a → List a × List a
splitAtNat = Haskell.Data.List.splitAtNat

splitAt : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → List a → List a × List a
splitAt = Haskell.Data.List.splitAt

lookup : ⦃ Eq a ⦄ → a → List (a × b) → Maybe b
lookup = Haskell.Data.List.lookup

null : ⦃ Foldable t ⦄ → t a → Bool
null = Haskell.Data.List.null

scanl : (b → a → b) → b → List a → List b
scanl = Haskell.Data.List.scanl

scanl1 : (a → a → a) → List a → List a
scanl1 = Haskell.Data.List.scanl1

scanr : (a → b → b) → b → List a → List b
scanr = Haskell.Data.List.scanr

scanr1 : (a → a → a) → List a → List a
scanr1 = Haskell.Data.List.scanr1

replicateNat : Nat → a → List a
replicateNat = Haskell.Data.List.replicateNat

replicate : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → a → List a
replicate = Haskell.Data.List.replicate

takeNat : Nat → List a → List a
takeNat = Haskell.Data.List.takeNat

take : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → List a → List a
take = Haskell.Data.List.take

dropNat : Nat → List a → List a
dropNat = Haskell.Data.List.dropNat

drop : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → List a → List a
drop = Haskell.Data.List.drop

takeWhile : (a → Bool) → List a → List a
takeWhile = Haskell.Data.List.takeWhile

dropWhile : (a → Bool) → List a → List a
dropWhile = Haskell.Data.List.dropWhile

filter : (a → Bool) → List a → List a
filter = Haskell.Data.List.filter

span : (a → Bool) → List a → List a × List a
span = Haskell.Data.List.span

break : (a → Bool) → List a → List a × List a
break = Haskell.Data.List.break

zip : List a → List b → List (a × b)
zip = Haskell.Data.List.zip

zip3 : List a → List b → List c → List (a × b × c)
zip3 = Haskell.Data.List.zip3

zipWith : (a → b → c) → List a → List b → List c
zipWith = Haskell.Data.List.zipWith

zipWith3 : (a → b → c → d) → List a → List b → List c → List d
zipWith3 = Haskell.Data.List.zipWith3

unzip : List (a × b) → List a × List b
unzip = Haskell.Data.List.unzip

unzip3 : List (a × b × c) → List a × List b × List c
unzip3 = Haskell.Data.List.unzip3

and : ⦃ Foldable t ⦄ → t Bool → Bool
and = Haskell.Data.List.and

or : ⦃ Foldable t ⦄ → t Bool → Bool
or = Haskell.Data.List.or

any : ⦃ Foldable t ⦄ → (a → Bool) → t a → Bool
any = Haskell.Data.List.any

all : ⦃ Foldable t ⦄ → (a → Bool) → t a → Bool
all = Haskell.Data.List.all

concat : ⦃ Foldable t ⦄ → t (List a) → List a
concat = Haskell.Data.List.concat

concatMap : ⦃ Foldable t ⦄ → (a → List b) → t a → List b
concatMap = Haskell.Data.List.concatMap

notElem : ⦃ Foldable t ⦄ → ⦃ Eq a ⦄ → a → t a → Bool
notElem = Haskell.Data.List.notElem


-- Problematic features:
--  - [Partial]:  Could pass implicit/instance arguments to prove totality.
--  - [Float]:    Or Float (Agda floats are Doubles)
--  - [Infinite]: Define colists and map to Haskell lists?

-- Missing from the Haskell Prelude:
--
--     Float        [Float]
--
--     Rational
--
--     Real(toRational),
--     Integral(quot, rem, div, mod, quotRem, divMod, toInteger),
--     Fractional((/), recip, fromRational),
--     Floating(pi, exp, log, sqrt, (**), logBase, sin, cos, tan,
--              asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh),
--     RealFrac(properFraction, truncate, round, ceiling, floor),
--     RealFloat(floatRadix, floatDigits, floatRange, decodeFloat,
--               encodeFloat, exponent, significand, scaleFloat, isNaN,
--               isInfinite, isDenormalized, isIEEE, isNegativeZero, atan2)
--
--     subtract, even, odd, gcd, lcm, (^), (^^),
--     fromIntegral, realToFrac
--
--     until [Partial]
--
--     iterate, repeat, cycle          [Infinite]
--
--     ReadS, Read(readsPrec, readList),
--     reads, readParen, read, lex
--
--     readIO, readLn,
--     IOError, ioError, userError


infixr 0 _$!_
_$!_ : (a → b) → a → b
_$!_ = _$_

seq : a → b → b
seq = const id

asTypeOf : a → a → a
asTypeOf x _ = x

undefined : {@0 @(tactic absurd) i : ⊥} → a
undefined {i = ()}

error : {@0 @(tactic absurd) i : ⊥} → String → a
error {i = ()} err

errorWithoutStackTrace : {@0 @(tactic absurd) i : ⊥} → String → a
errorWithoutStackTrace {i = ()} err


coerce : @0 a ≡ b → a → b
coerce refl x = x

IsJust : Maybe a → Type
IsJust Nothing  = ⊥
IsJust (Just _) = ⊤
