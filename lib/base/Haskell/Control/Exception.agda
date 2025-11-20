module Haskell.Control.Exception where

open import Haskell.Prim
open import Haskell.Prim.Either
open import Haskell.Prim.Eq
open import Haskell.Prim.Functor
open import Haskell.Prim.IO
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monad
open import Haskell.Prim.Ord
open import Haskell.Prim.Show
open import Haskell.Prim.String

open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement

private variable
  e1 e2 : Set

record Exception (e : Set) : Set where
  no-eta-equality
  field
    overlap {{iShow}} : Show e
    displayException : e → String
open Exception {{...}} public

{-# COMPILE AGDA2HS Exception existing-class #-}

postulate
  IOException : Set
  instance
    iEqIOException : Eq IOException
    iExceptionIOException : Exception IOException

data ArithException : Set where
  Overflow UnderFlow LossOfPrecision DivideByZero Denormal : ArithException
  RatioZeroDenominator : ArithException

postulate instance
  iOrdArithException : Ord ArithException
  iExceptionArithException : Exception ArithException

data ArrayException : Set where
  IndexOutOfBounds UndefinedElement : String → ArrayException

postulate instance
  iOrdArrayException : Ord ArrayException
  iExceptionArrayException : Exception ArrayException

record AssertionFailed : Set where
  no-eta-equality; pattern
  field theFailedAssertion : String

postulate instance
  iExceptionAssertionFailed : Exception AssertionFailed

record NoMethodError : Set where
  no-eta-equality; pattern
  field theNoMethodError : String

postulate instance
  iExceptionNoMethodError : Exception NoMethodError

record PatternMatchFail : Set where
  no-eta-equality; pattern
  field thePatternMatchFail : String

postulate instance
  iExceptionPatternMatchFail : Exception PatternMatchFail

record RecConError : Set where
  no-eta-equality; pattern
  field theRecConError : String

postulate instance
  iExceptionRecConError : Exception RecConError

record RecSelError : Set where
  no-eta-equality; pattern
  field theRecSelError : String

postulate instance
  iExceptionRecSelError : Exception RecSelError

record RecUpdError : Set where
  no-eta-equality; pattern
  field theRecUpdError : String

postulate instance
  iExceptionRecUpdError : Exception RecUpdError

record ErrorCall : Set where
  no-eta-equality; pattern
  field theErrorCall : String

postulate instance
  iOrdErrorCall : Ord ErrorCall
  iExceptionErrorCall : Exception ErrorCall

record TypeError : Set where
  no-eta-equality; pattern
  field theTypeError : String

postulate instance
  iExceptionTypeError : Exception TypeError

postulate
  @0 MayThrow : Set → Set

  throw : {{Exception e}} → @0 {{MayThrow e}} → e → a
  throwIO : {{Exception e}} → @0 {{MayThrow e}} → e → IO a

postulate
  catch : {{Exception e}} → (@0 {{MayThrow e}} → IO a) → (e → IO a) → IO a
  catchJust : {{Exception e}} → (e → Maybe b) → (@0 {{MayThrow e}} → IO a) → (b → IO a) → IO a

handle : {{Exception e}} → (e → IO a) → (@0 {{MayThrow e}} → IO a) → IO a
handle = flip catch

handleJust : {{Exception e}} → (e → Maybe b) → (b → IO a) → (@0 {{MayThrow e}} → IO a) → IO a
handleJust f = flip (catchJust f)

try : {{Exception e}} → (@0 {{MayThrow e}} → IO a) → IO (Either e a)
try a = catch (fmap Right a) (return ∘ Left)

tryJust : {{Exception e}} → (e → Maybe b) → (@0 {{MayThrow e}} → IO a) → IO (Either b a)
tryJust p a = catchJust p (fmap Right a) (return ∘ Left)

postulate
  evaluate : a → IO a
  mapException : {{Exception e1}} → {{Exception e2}} → (e1 → e2) → a → a

assert : @0 {{MayThrow AssertionFailed}} → (@0 b : Type ℓ) → {{Dec b}} → (@0 {{b}} → a) → a
assert _ {{True  ⟨ p ⟩}} x = x {{p}}
assert _ {{False ⟨ _ ⟩}} x = throw oops
  where postulate oops : AssertionFailed

postulate
  bracket : IO a → (a → IO b) → (a → IO c) → IO c
  bracket_ : IO a → IO b → IO c → IO c
  bracketOnError : IO a → (a → IO b) → (a → IO c) → IO c
  finally : IO a → IO b → IO a
  onException : IO a → IO b → IO a

ioException : @0 {{MayThrow IOException}} → IOException → IO a
ioException = throwIO
