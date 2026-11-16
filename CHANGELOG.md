Release notes for agda2hs v1.5
==============================

Changes to agda2hs
------------------

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
- `assert` now takes an erased argument of type `MayThrow AssertionFailed`,
  which is propagated to any function that calls it.
- The `TypeError` data type in `Haskell.Prim` has been renamed to
  `UnsatisfiedConstraint`, to avoid a clash with the `TypeError` exception
  type added to `Haskell.Control.Exception`.
- Added the `existing` keyword to the `COMPILE AGDA2HS` pragma, which skips
  code generation for a definition whose Haskell implementation is provided by
  a `FOREIGN` pragma. Such definitions are still exported. The
  `existing-class` keyword is now restricted to records (see issue #447).
- A record marked with `existing` is treated as opaque: projecting one of its
  fields is rejected, because the corresponding Haskell type may not export a
  field selector. The exception records in `Haskell.Control.Exception` are
  marked with `existing` accordingly.

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
  A function that may raise an exception takes an erased `MayThrow` argument
  recording the exception type (see issue #432).
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
