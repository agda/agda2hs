module Haskell.Control.Exception where

open import Haskell.Prim
open import Haskell.Prim.Either
open import Haskell.Prim.Eq
open import Haskell.Prim.Functor
open import Haskell.Prim.IO
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monad
open import Haskell.Prim.Show
open import Haskell.Prim.String

open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement

record Exception (e : Set) : Set where
  no-eta-equality
  field
    overlap {{iShow}} : Show e
    displayException : e → String

postulate
  IOException : Set
  instance
    iEqIOException : Eq IOException
    iExceptionIOException : Exception IOException

  AssertionFailed : Set
  instance
    iExceptionAssertionFailed : Exception AssertionFailed

postulate
  @0 MayThrow : Set → Set

  throw : {{Exception e}} → @0 {{MayThrow e}} → e → a
  throwIO : {{Exception e}} → @0 {{MayThrow e}} → e → IO a

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

assert : @0 {{MayThrow AssertionFailed}} → (@0 b : Type ℓ) → {{Dec b}} → (@0 {{b}} → a) → a
assert _ {{True  ⟨ p ⟩}} x = x {{p}}
assert _ {{False ⟨ _ ⟩}} x = throw oops
  where postulate oops : AssertionFailed
