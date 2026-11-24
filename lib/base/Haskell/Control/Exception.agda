module Haskell.Control.Exception where

open import Haskell.Prim
open import Haskell.Prim.Applicative
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
  Overflow Underflow LossOfPrecision DivideByZero Denormal : ArithException
  RatioZeroDenominator : ArithException

postulate instance
  iOrdArithException : Ord ArithException
  iExceptionArithException : Exception ArithException

data ArrayException : Set where
  IndexOutOfBounds UndefinedElement : String → ArrayException

postulate instance
  iOrdArrayException : Ord ArrayException
  iExceptionArrayException : Exception ArrayException

-- The exception types below are Haskell newtypes wrapping a single @String@.
-- They are modelled as Agda records so that values can be constructed with
-- record syntax and inspected by pattern matching. However, the corresponding
-- Haskell types do not export a field selector, so the record modules are not
-- opened publicly. Projecting a field of these records is therefore rejected,
-- while construction and pattern matching still work.

record AssertionFailed : Set where
  no-eta-equality; pattern
  field theFailedAssertion : String
{-# COMPILE AGDA2HS AssertionFailed existing #-}

postulate instance
  iExceptionAssertionFailed : Exception AssertionFailed

record NoMethodError : Set where
  no-eta-equality; pattern
  field theNoMethodError : String
{-# COMPILE AGDA2HS NoMethodError existing #-}

postulate instance
  iExceptionNoMethodError : Exception NoMethodError

record PatternMatchFail : Set where
  no-eta-equality; pattern
  field thePatternMatchFail : String
{-# COMPILE AGDA2HS PatternMatchFail existing #-}

postulate instance
  iExceptionPatternMatchFail : Exception PatternMatchFail

record RecConError : Set where
  no-eta-equality; pattern
  field theRecConError : String
{-# COMPILE AGDA2HS RecConError existing #-}

postulate instance
  iExceptionRecConError : Exception RecConError

record RecSelError : Set where
  no-eta-equality; pattern
  field theRecSelError : String
{-# COMPILE AGDA2HS RecSelError existing #-}

postulate instance
  iExceptionRecSelError : Exception RecSelError

record RecUpdError : Set where
  no-eta-equality; pattern
  field theRecUpdError : String
{-# COMPILE AGDA2HS RecUpdError existing #-}

postulate instance
  iExceptionRecUpdError : Exception RecUpdError

record ErrorCall : Set where
  no-eta-equality; pattern
  field theErrorCall : String
{-# COMPILE AGDA2HS ErrorCall existing #-}

postulate instance
  iOrdErrorCall : Ord ErrorCall
  iExceptionErrorCall : Exception ErrorCall

record TypeError : Set where
  no-eta-equality; pattern
  field theTypeError : String
{-# COMPILE AGDA2HS TypeError existing #-}

postulate instance
  iExceptionTypeError : Exception TypeError

-- | The @MayThrow@ monad marks computations that may throw an exception of
-- type @e@. On the Haskell side it is compiled to the identity monad:
-- @MayThrow e a@ becomes just @a@ and the constructors are erased. Hence the
-- constructors cannot be pattern matched in functions that are compiled to
-- Haskell.
data MayThrow (e : Set) (a : Set) : Set where
  ok : a → MayThrow e a
  throw  : {{Exception e}} → e → MayThrow e a

bindMayThrow : MayThrow e a → (a → MayThrow e b) → MayThrow e b
bindMayThrow (ok x) f = f x
bindMayThrow (throw ⦃ i ⦄ e) f = throw ⦃ i ⦄ e

instance
  iFunctorMayThrow : Functor (MayThrow e)
  iFunctorMayThrow = record {DefaultFunctor iDefaultFunctorMayThrow}
    where
      iDefaultFunctorMayThrow : DefaultFunctor (MayThrow e)
      iDefaultFunctorMayThrow .DefaultFunctor.fmap f m = bindMayThrow m (ok ∘ f)

  iApplicativeMayThrow : Applicative (MayThrow e)
  iApplicativeMayThrow = record {DefaultApplicative iDefaultApplicativeMayThrow}
    where
      iDefaultApplicativeMayThrow : DefaultApplicative (MayThrow e)
      iDefaultApplicativeMayThrow .DefaultApplicative.pure = ok
      iDefaultApplicativeMayThrow .DefaultApplicative._<*>_ mf mx =
        bindMayThrow mf λ f → bindMayThrow mx λ x → ok (f x)

  iMonadMayThrow : Monad (MayThrow e)
  iMonadMayThrow = record {DefaultMonad iDefaultMonadMayThrow}
    where
      iDefaultMonadMayThrow : DefaultMonad (MayThrow e)
      iDefaultMonadMayThrow .DefaultMonad._>>=_ = bindMayThrow

postulate
  throwIO : {{Exception e}} → e → IO a

postulate
  catch : {{Exception e}} → IO a → (e → IO a) → IO a
  catchJust : {{Exception e}} → (e → Maybe b) → IO a → (b → IO a) → IO a

handle : {{Exception e}} → (e → IO a) → IO a → IO a
handle = flip catch

handleJust : {{Exception e}} → (e → Maybe b) → (b → IO a) → IO a → IO a
handleJust f = flip (catchJust f)

try : {{Exception e}} → IO a → IO (Either e a)
try a = catch (fmap Right a) (pure ∘ Left)

tryJust : {{Exception e}} → (e → Maybe b) → IO a → IO (Either b a)
tryJust p a = catchJust p (fmap Right a) (pure ∘ Left)

postulate
  evaluate : a → IO a
  mapException : {{Exception e1}} → {{Exception e2}} → (e1 → e2) → a → a

assert : (@0 b : Type ℓ) → {{Dec b}} → (@0 {{b}} → a) → MayThrow AssertionFailed a
assert _ {{True  ⟨ p ⟩}} x = ok (x {{p}})
assert _ {{False ⟨ _ ⟩}} x = throw oops
  where postulate oops : AssertionFailed

postulate
  bracket : IO a → (a → IO b) → (a → IO c) → IO c
  bracket_ : IO a → IO b → IO c → IO c
  bracketOnError : IO a → (a → IO b) → (a → IO c) → IO c
  finally : IO a → IO b → IO a
  onException : IO a → IO b → IO a
