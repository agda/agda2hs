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
open import Haskell.Prim.Char           public
open import Haskell.Prim.Double         public
open import Haskell.Prim.Either         public
open import Haskell.Prim.Enum           public
open import Haskell.Prim.Eq             public
open import Haskell.Prim.Int            public
open import Haskell.Prim.Integer        public
open import Haskell.Prim.IO             public
  hiding (returnIO; bindIO; failIO; mplusIO)
open import Haskell.Prim.Maybe          public
open import Haskell.Prim.Monoid         public
open import Haskell.Prim.MonadFail      public
open import Haskell.Prim.Num            public
open import Haskell.Prim.Ord            public
open import Haskell.Prim.Show           public
open import Haskell.Prim.Tuple          public hiding (first; second; _***_)
open import Haskell.Prim.Word           public
open import Haskell.Prim.String         public
open import Haskell.Prim.Functor        public
open import Haskell.Prim.Applicative    public
open import Haskell.Prim.Monad          public
open import Haskell.Prim.Traversable    public
open import Haskell.Prim.Foldable       public
  hiding (fold; foldMap'; foldr'; toList; null; length)

open import Haskell.Data.String         public
  using (lines; words; unlines; unwords)
open import Haskell.Data.List           public
  using (_++_; map; reverse; lengthNat; length;
         head; last; tail; init;
         _!!ᴺ_; _!!_; splitAt; lookup; null;
         scanl; scanl1; scanr; scanr1;
         replicateNat; replicate;
         take; drop; takeWhile; dropWhile;
         filter; span; break;
         zip; zip3; zipWith; zipWith3; unzip; unzip3;
         and; or; any; all; concat; concatMap; notElem)
open import Haskell.Data.Functor        public using (_<$>_)
open import Haskell.Control.Monad       public using (_=<<_; mapM₋; sequence₋)


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