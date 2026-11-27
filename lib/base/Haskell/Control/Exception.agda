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
{-# COMPILE AGDA2HS IOException existing #-}

data ArithException : Set where
  Overflow Underflow LossOfPrecision DivideByZero Denormal : ArithException
  RatioZeroDenominator : ArithException
{-# COMPILE AGDA2HS ArithException existing #-}

postulate instance
  iOrdArithException : Ord ArithException
  iExceptionArithException : Exception ArithException

data ArrayException : Set where
  IndexOutOfBounds UndefinedElement : String → ArrayException
{-# COMPILE AGDA2HS ArrayException existing #-}

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
--
-- This makes the definition of @throw@ sound on the Agda side, since there is
-- no way to obtain an @a@ from a @MayThrow e a@. However, it does not prevent
-- code whose type does not mention @MayThrow@ from throwing an exception:
-- because @MayThrow e a@ is compiled to @a@, a value of this type can still be
-- forced by strict code (a strict field, @seq@, ...), which raises the
-- exception at that point.
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
  iApplicativeMayThrow = record {ApplicativeFrom<*> iDefaultApplicativeMayThrow}
    where
      iDefaultApplicativeMayThrow : ApplicativeFrom<*> (MayThrow e)
      iDefaultApplicativeMayThrow .ApplicativeFrom<*>.pure = ok
      iDefaultApplicativeMayThrow .ApplicativeFrom<*>._<*>_ mf mx =
        bindMayThrow mf λ f → bindMayThrow mx λ x → ok (f x)

  iMonadMayThrow : Monad (MayThrow e)
  iMonadMayThrow = record {DefaultMonad iDefaultMonadMayThrow}
    where
      iDefaultMonadMayThrow : DefaultMonad (MayThrow e)
      iDefaultMonadMayThrow .DefaultMonad._>>=_ = bindMayThrow

-- | The monad transformer corresponding to the @MayThrow@ monad. A value of
-- type @MayThrowT e m a@ is an action in @m@ that may throw an exception of
-- type @e@. It is compiled to @m a@, so the monad is inherited from @m@.
record MayThrowT (e : Set) (m : Type → Type) (a : Set) : Set where
  constructor mkMayThrowT
  field runMayThrowT : m (MayThrow e a)
open MayThrowT public
{-# COMPILE AGDA2HS MayThrowT unboxed #-}

-- | Throw an exception in the @MayThrowT@ monad transformer.
throwT : ⦃ Applicative m ⦄ → ⦃ Exception e ⦄ → e → MayThrowT e m a
throwT e = mkMayThrowT (pure (throw e))
{-# COMPILE AGDA2HS throwT inline #-}

-- | Lift an action in @m@ into the @MayThrowT@ monad transformer.
liftMayThrowT : ⦃ Functor m ⦄ → m a → MayThrowT e m a
liftMayThrowT x = mkMayThrowT (fmap ok x)
{-# COMPILE AGDA2HS liftMayThrowT inline #-}

instance
  iDefaultFunctorMayThrowT : ⦃ Functor m ⦄ → DefaultFunctor (MayThrowT e m)
  iDefaultFunctorMayThrowT .DefaultFunctor.fmap f x =
    mkMayThrowT (fmap (fmap ⦃ iFunctorMayThrow ⦄ f) (runMayThrowT x))

  iFunctorMayThrowT : ⦃ Functor m ⦄ → Functor (MayThrowT e m)
  iFunctorMayThrowT = record {DefaultFunctor iDefaultFunctorMayThrowT}

  iDefaultApplicativeMayThrowT : ⦃ Applicative m ⦄
                              → ApplicativeFrom<*> (MayThrowT e m)
  iDefaultApplicativeMayThrowT .ApplicativeFrom<*>.pure x =
    mkMayThrowT (pure (ok x))
  iDefaultApplicativeMayThrowT .ApplicativeFrom<*>._<*>_ mf mx =
    mkMayThrowT (_<*>_ (fmap (_<*>_ ⦃ iApplicativeMayThrow ⦄)
                              (runMayThrowT mf))
                       (runMayThrowT mx))

  iApplicativeMayThrowT : ⦃ Applicative m ⦄ → Applicative (MayThrowT e m)
  iApplicativeMayThrowT = record {ApplicativeFrom<*> iDefaultApplicativeMayThrowT}

  iDefaultMonadMayThrowT : ⦃ Monad m ⦄ → DefaultMonad (MayThrowT e m)
  iDefaultMonadMayThrowT .DefaultMonad._>>=_ x k =
    mkMayThrowT (_>>=_ (runMayThrowT x) λ where
      (ok y)              → runMayThrowT (k y)
      (throw ⦃ i ⦄ err)   → pure (throw ⦃ i ⦄ err))

  iMonadMayThrowT : ⦃ Monad m ⦄ → Monad (MayThrowT e m)
  iMonadMayThrowT = record {DefaultMonad iDefaultMonadMayThrowT}

postulate
  throwIO : {{Exception e}} → e → IO a
{-# COMPILE AGDA2HS throwIO existing #-}

postulate
  catch : {{Exception e}} → IO a → (e → IO a) → IO a
  catchJust : {{Exception e}} → (e → Maybe b) → IO a → (b → IO a) → IO a
{-# COMPILE AGDA2HS catch existing #-}
{-# COMPILE AGDA2HS catchJust existing #-}

handle : {{Exception e}} → (e → IO a) → IO a → IO a
handle = flip catch
{-# COMPILE AGDA2HS handle existing #-}

handleJust : {{Exception e}} → (e → Maybe b) → (b → IO a) → IO a → IO a
handleJust f = flip (catchJust f)
{-# COMPILE AGDA2HS handleJust existing #-}

try : {{Exception e}} → IO a → IO (Either e a)
try a = catch (fmap Right a) (pure ∘ Left)
{-# COMPILE AGDA2HS try existing #-}

tryJust : {{Exception e}} → (e → Maybe b) → IO a → IO (Either b a)
tryJust p a = catchJust p (fmap Right a) (pure ∘ Left)
{-# COMPILE AGDA2HS tryJust existing #-}

postulate
  evaluate : a → IO a
  mapException : {{Exception e1}} → {{Exception e2}} → (e1 → e2) → a → a
{-# COMPILE AGDA2HS evaluate existing #-}
{-# COMPILE AGDA2HS mapException existing #-}

-- | The monad morphism from @MayThrow@ to @IO@. Since @MayThrow e a@ is
-- compiled to @a@, this is compiled to @return@.
postulate
  runMayThrow : MayThrow e a → IO a

assert : (@0 b : Type ℓ) → {{Dec b}} → (@0 {{b}} → a) → MayThrow AssertionFailed a
assert _ {{True  ⟨ p ⟩}} x = ok (x {{p}})
assert _ {{False ⟨ _ ⟩}} x = throw oops
  where postulate oops : AssertionFailed
{-# COMPILE AGDA2HS assert existing #-}

postulate
  bracket : IO a → (a → IO b) → (a → IO c) → IO c
  bracket_ : IO a → IO b → IO c → IO c
  bracketOnError : IO a → (a → IO b) → (a → IO c) → IO c
  finally : IO a → IO b → IO a
  onException : IO a → IO b → IO a
{-# COMPILE AGDA2HS bracket existing #-}
{-# COMPILE AGDA2HS bracket_ existing #-}
{-# COMPILE AGDA2HS bracketOnError existing #-}
{-# COMPILE AGDA2HS finally existing #-}
{-# COMPILE AGDA2HS onException existing #-}
