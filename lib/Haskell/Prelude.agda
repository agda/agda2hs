{-# OPTIONS --no-auto-inline #-}
module Haskell.Prelude where

open import Haskell.Prim
open Haskell.Prim public using
  ( Bool; True; False; Char; Integer;
    List; []; _∷_; Nat; zero; suc; ⊤; tt;
    TypeError; ⊥; iNumberNat; IsTrue; IsFalse;
    All; allNil; allCons; NonEmpty; lengthNat;
    id; _∘_; _$_; flip; const;
    if_then_else_; case_of_;
    Number; fromNat; Negative; fromNeg;
    IsString; fromString;
    _≡_; refl;
    a; b; c; d; e; f; m; s; t )

open import Haskell.Prim.Absurd      public
open import Haskell.Prim.Applicative public
open import Haskell.Prim.Bool        public
open import Haskell.Prim.Bounded     public
open import Haskell.Prim.Double      public
open import Haskell.Prim.Either      public
open import Haskell.Prim.Enum        public
open import Haskell.Prim.Eq          public
open import Haskell.Prim.Foldable    public
open import Haskell.Prim.Functor     public
open import Haskell.Prim.Int         public
open import Haskell.Prim.Integer     public
open import Haskell.Prim.IO          public
open import Haskell.Prim.List        public
open import Haskell.Prim.Maybe       public
open import Haskell.Prim.Monad       public
open import Haskell.Prim.Monoid      public
open import Haskell.Prim.Num         public
open import Haskell.Prim.Ord         public
open import Haskell.Prim.Show        public
open import Haskell.Prim.String      public
open import Haskell.Prim.Traversable public
open import Haskell.Prim.Tuple       public hiding (first; second; _***_)
open import Haskell.Prim.Word        public

open import Haskell.Law              public
open import Haskell.Law.Applicative  public
open import Haskell.Law.Bool         public
open import Haskell.Law.Eq           public
open import Haskell.Law.Equality     public
open import Haskell.Law.Functor      public
open import Haskell.Law.List         public
open import Haskell.Law.Maybe        public
open import Haskell.Law.Monad        public
open import Haskell.Law.Monoid       public
open import Haskell.Law.Ord          public

-- Problematic features
--  - [Partial]:  Could pass implicit/instance arguments to prove totality.
--  - [Float]:    Or Float (Agda floats are Doubles)
--  - [Infinite]: Define colists and map to Haskell lists?

-- Missing from the Haskell Prelude:
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


-------------------------------------------------
-- More List functions
--   These uses Eq, Ord, or Foldable, so can't go in Prim.List without
--   turning those dependencies around.

reverse : List a → List a
reverse = foldl (flip _∷_) []

infixl 9 _!!_ _!!ᴺ_

_!!ᴺ_ : (xs : List a) (n : Nat) → @0 ⦃ IsTrue (n < lengthNat xs) ⦄ → a
(x ∷ xs) !!ᴺ zero  = x
(x ∷ xs) !!ᴺ suc n = xs !!ᴺ n

_!!_ : (xs : List a) (n : Int)
     → ⦃ @0 nn : IsNonNegativeInt n ⦄
     → ⦃ @0 _  : IsTrue (intToNat n {{nn}} < lengthNat xs) ⦄ → a
xs !! n = xs !!ᴺ intToNat n

lookup : ⦃ Eq a ⦄ → a → List (a × b) → Maybe b
lookup x []              = Nothing
lookup x ((x₁ , y) ∷ xs) = if x == x₁ then Just y else lookup x xs
