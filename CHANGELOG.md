Release notes for agda2hs v1.5
==============================

Changes to agda2hs
------------------

- Compiling two definitions with the same Haskell name is now rejected with a
  proper error message. This can happen for definitions in local modules, since
  Haskell does not have local modules (see issue #122).
- Proper where-provenance so that subsequent anonymous modules with `module _`
  are no longer mistaken for local `where` definitions (see issue #463).
- The error message for clashing imports now includes the source location of
  the definition that triggered the import (see issue #157).
- The constructor of a record without an explicitly named constructor is now
  imported together with the record type when used from another module
  (see issue #454).
- Pragma information (such as `inline` and `COMPILE ... to`) is now also
  recorded for modules that are skipped because they are already up-to-date.
  Previously this could result in names not being compiled away when
  recompiling only a downstream module (see issue #486).
- Postulates in a `where` block are now compiled to a runtime error instead of
  crashing the compiler. Declarations other than functions and postulates are
  rejected with a proper error message (see issue #443).
- The `Traversable` instances in the Prelude are now defined directly using
  copatterns and default instances instead of the `traverse=` helper, so that
  they pass the instance validity check (see issue #457).
- Exceptions can now only be thrown in the `MayThrow` monad. This monad is
  compiled to the identity monad, i.e. `MayThrow e a` is compiled to just `a`
  and its constructors are erased, so they cannot be pattern matched in
  functions that are compiled to Haskell. Functions that may throw (such as
  `assert` and `throw`) now return a value in this monad instead of taking an
  erased `MayThrow` argument. Since a value of type `MayThrow e a` cannot be
  used where an `a` is expected, a check can no longer be silently erased
  (see issue #428).
- The `TypeError` data type in `Haskell.Prim` has been renamed to
  `UnsatisfiedConstraint`, to avoid a clash with the `TypeError` exception
  type added to `Haskell.Control.Exception`.
- Added the `existing` keyword to the `COMPILE AGDA2HS` pragma, which skips
  code generation for a definition whose Haskell implementation is provided by
  a `FOREIGN` pragma. Such definitions are still exported. The
  `existing-class` keyword is now restricted to records (see issue #447).
- The Haskell selectors of a record are only exported if the record module is
  opened publicly (`open R public`) in the module that defines the record.
  Otherwise the record is still exported with its constructor, but a projection
  of one of its fields is rejected. This also applies to records marked with
  `existing`, so their fields can be kept private when the corresponding
  Haskell type does not export a selector.
- Added the `gadt` keyword to the `COMPILE AGDA2HS` pragma, which compiles a
  datatype using Haskell GADT syntax, with the result type of each constructor
  written out explicitly (see issue #242).
- Forced (dot) patterns in non-erased positions are now only rejected if the
  clause also matches a constructor in an erased position. This allows refining
  types by matching on a non-erased equality constraint, while still rejecting
  the unsafe coercion from issue #142 (see issue #494).

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.5+is%3Apr for the full list of changes.

Additions to the agda2hs Prelude
--------------------------------

- Added `predNat` to `Haskell.Extra.Nat`: the predecessor of a nonzero
  natural number, returning the predecessor together with a proof that
  the original number is its successor. It compiles to Haskell's `pred`
  and enables defining functions such as a `Nat` recursor on top of
  `ifDec` (see issue #385).
- Added bindings for the numeric type classes `Real`, `Integral`,
  `Fractional`, `Floating`, `RealFrac`, and `RealFloat`, together with the
  `Rational` type. Instances for the standard numeric types are postulated
  for now (see issue #262).
- Added basic support for Haskell exceptions in `Haskell.Control.Exception`.
  A function that may raise an exception returns a value in the `MayThrow`
  monad, which records the exception type in its type (see issue #432).
- Added `Functor`, `Applicative`, and `Monad` instances for `Delay` in
  `Haskell.Extra.Delay`. Like `MayThrow`, `Delay` is a *transparent* monad:
  it is compiled to the identity monad, so its class methods are compiled to
  their identity counterparts.
- Added bindings to `System.Environment` in `Haskell.System.Environment`
  (see issue #433).

Changes to agda2hs-containers
-----------------------------

- `prop-member-map` in `Haskell.Data.Set` now states only that
  `member x s ≡ True` implies `member (f x) (map f s) ≡ True`. The previous
  equation does not hold for non-injective `f` and could be used to prove
  `⊥` (see issue #487).

Fixed issues
------------

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.5+is%3Aissue for the full list of fixed issues.
