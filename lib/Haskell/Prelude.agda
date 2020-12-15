{-# OPTIONS --no-auto-inline #-}
module Haskell.Prelude where

open import Agda.Builtin.Unit         public
open import Agda.Builtin.Nat as Nat   public hiding (_==_; _<_; _+_; _*_; _-_)
open import Agda.Builtin.List         public
open import Agda.Builtin.Bool         public
open import Agda.Builtin.Char         public
open import Agda.Builtin.FromString   public
import Agda.Builtin.String as Str
open import Agda.Builtin.Strict
open import Agda.Builtin.Word         public renaming (Word64 to Word)
open import Agda.Builtin.Equality     public
open import Agda.Builtin.Int using (pos; negsuc)

open import Haskell.Prim
open Haskell.Prim public using ( TypeError; ⊥; iNumberNat; IsTrue; IsFalse;
                                 All; allNil; allCons; NonEmpty; lengthNat;
                                 id; _∘_; _$_; flip; const;
                                 if_then_else_; case_of_;
                                 Number; fromNat; Negative; fromNeg;
                                 a; b; c; d; e; f; m; s; t )

open import Haskell.Prim.Absurd

open import Haskell.Prim.Integer
open Haskell.Prim.Integer public using (Integer; iNumberInteger; iNegativeInteger; isNegativeInteger; IsNonNegativeInteger)

open import Haskell.Prim.Int renaming (Int64 to Int)
open Haskell.Prim.Int public using (iNumberInt; iNegativeInt; isNegativeInt; IsNonNegativeInt) renaming (Int64 to Int)

open import Haskell.Prim.Double
open Haskell.Prim.Double public using (iNumberDouble; iNegativeDouble; Double)

open import Haskell.Prim.Word

open import Haskell.Prim.Bool            public
open import Haskell.Prim.List            public
open import Haskell.Prim.Maybe           public
open import Haskell.Prim.Either          public
open import Haskell.Prim.Tuple  as Tuple public hiding (first; second; _***_)
open import Haskell.Prim.Eq              public
open import Haskell.Prim.Ord             public
open import Haskell.Prim.Monoid          public
open import Haskell.Prim.Num             public
open import Haskell.Prim.Foldable        public
open import Haskell.Prim.String          public
open import Haskell.Prim.Show            public
open import Haskell.Prim.Functor         public
open import Haskell.Prim.Applicative     public
open import Haskell.Prim.Monad           public
open import Haskell.Prim.Traversable     public

-- Problematic features
--  - [Partial]:  Could pass implicit/instance arguments to prove totality.
--  - [Float]:    Or Float (Agda floats are Doubles)
--  - [Infinite]: Define colists and map to Haskell lists?

-- Missing from the Haskell Prelude:
--
--     Enum(succ, pred, toEnum, fromEnum, enumFrom, enumFromThen,
--          enumFromTo, enumFromThenTo),      [Partial]
--     Bounded(minBound, maxBound),
--
--     Float        [Float]
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
--               isInfinite, isDenormalized, isIEEE, isNegativeZero, atan2),
--
--     subtract, even, odd, gcd, lcm, (^), (^^),
--     fromIntegral, realToFrac,
--
--     foldr1, foldl1, maximum, minimum      [Partial]
--
--     until [Partial]
--
--     iterate, repeat, cycle          [Infinite]
--
--     ReadS, Read(readsPrec, readList),
--     reads, readParen, read, lex,
--
--     IO, putChar, putStr, putStrLn, print,
--     getChar, getLine, getContents, interact,
--     FilePath, readFile, writeFile, appendFile, readIO, readLn,
--     IOError, ioError, userError,


--------------------------------------------------
-- Functions

infixr 0 _$!_
_$!_ : (a → b) → a → b
f $! x = primForce x f

seq : a → b → b
seq x y = const y $! x

asTypeOf : a → a → a
asTypeOf x _ = x

undefined : {@(tactic absurd) i : ⊥} → a
undefined {i = ()}

error : {@(tactic absurd) i : ⊥} → String → a
error {i = ()} err

errorWithoutStackTrace : {@(tactic absurd) i : ⊥} → String → a
errorWithoutStackTrace {i = ()} err


-------------------------------------------------
-- More List functions
--   These uses Eq, Ord, or Foldable, so can't go in Prim.List without
--   turning those dependencies around.

reverse : List a → List a
reverse = foldl (flip _∷_) []

infixl 9 _!!_ _!!ᴺ_

_!!ᴺ_ : (xs : List a) (n : Nat) → ⦃ IsTrue (n < lengthNat xs) ⦄ → a
(x ∷ xs) !!ᴺ zero  = x
(x ∷ xs) !!ᴺ suc n = xs !!ᴺ n

_!!_ : (xs : List a) (n : Int) ⦃ nn : IsNonNegativeInt n ⦄ → ⦃ IsTrue (intToNat n < lengthNat xs) ⦄ → a
xs !! n = xs !!ᴺ intToNat n

lookup : ⦃ Eq a ⦄ → a → List (a × b) → Maybe b
lookup x []              = Nothing
lookup x ((x₁ , y) ∷ xs) = if x == x₁ then Just y else lookup x xs
