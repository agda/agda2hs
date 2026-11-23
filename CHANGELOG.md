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
- The `to` keyword of the `COMPILE AGDA2HS` pragma is now also supported for
  instances. An instance for a type that is compiled to another type with a
  `to` pragma must itself be given a `to` pragma pointing to the corresponding
  instance of the target type. This prevents the generation of duplicate
  instances. agda2hs warns if the two compiled instances do not match, or if
  the comparison cannot be performed (for instance because the target uses a
  feature that agda2hs does not support, such as multi-argument pattern
  lambdas); the target instance is the one that is used in the generated code
  either way (see issue #269).
- A datatype from a primitive module (such as `Bool` or `Maybe`) can now be
  the target of a compile-to pragma without having a `COMPILE` pragma of its
  own.
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
  A function that may raise an exception takes an erased `MayThrow` argument
  recording the exception type (see issue #432).
- Added bindings to `System.Environment` in `Haskell.System.Environment`
  (see issue #433).

Changes to the agda2hs Prelude
------------------------------

- The `Word` laws in `Haskell.Law.Num.Word` are now derived from the fact that
  `n2w` is a surjective homomorphism from `Nat` to `Word`. The previous
  postulates that `w2n` preserves addition and multiplication ignored wrapping
  modulo 2⁶⁴ and could be used to prove `⊥` (see issue #499).
- The `Double` definitions of `negate`, `abs` and `signum` in
  `Haskell.Prim.Num`, and of `max` and `min` in `Haskell.Prim.Ord`, now agree
  with GHC's Prelude on signed zeros and NaN (see issue #500).

Changes to agda2hs-containers
-----------------------------

- `prop-member-map` in `Haskell.Data.Set` now states only that
  `member x s ≡ True` implies `member (f x) (map f s) ≡ True`. The previous
  equation does not hold for non-injective `f` and could be used to prove
  `⊥` (see issue #487).

Fixed issues
------------

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.5+is%3Aissue for the full list of fixed issues.
