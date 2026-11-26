Release notes for agda2hs v1.5
==============================

Changes to agda2hs
------------------

- Increased the Agda base version to 2.9.0.
- Increased bounds to support GHC 9.14.1.
- Added support for `COMPILE AGDA2HS ... to ...` pragmas, which compile a
  datatype or function to an existing Haskell definition instead of generating
  new code. agda2hs checks that the compiled definition matches the target;
  mismatches in the names of constructors or in the clauses of a function are
  reported as warnings, while other mismatches are errors (see issue #155).
- Non-erased propositional equality in an instance argument is now compiled to
  a Haskell equality constraint, e.g. `⦃ a ≡ b ⦄` becomes `a ~ b =>`
  (see issue #140).
- Each compiled module now has an explicit export list of the definitions that
  are public in Agda and are not compiled away (for example inline,
  transparent, unboxed, tuple, and compile-to definitions are omitted). The
  `TypeOperators` extension is enabled automatically when the export list
  contains a type operator (see issue #44).
- The `inline` pragma can now be used on any function, not only on
  single-clause functions that match on variables or transparent record
  constructors. If a function marked `inline` is not inlined at a call site,
  agda2hs reports an error (see issue #259).
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
  instances. An instance for a type that is compiled to another type (either
  with a `to` pragma, or because it is an unboxed or tuple record) must itself
  be given a `to` pragma pointing to the corresponding instance of the target
  type. This prevents the generation of duplicate instances. agda2hs warns if
  the two compiled instances do not match, or if the comparison cannot be
  performed (for instance because the target uses a feature that agda2hs does
  not support, such as multi-argument pattern lambdas); the target instance is
  the one that is used in the generated code either way (see issue #269). An
  instance whose every clause just applies the method being defined to its
  arguments (such as `x == y = x == y`) is accepted, since it defers to the
  instance it is compiled to.
- A datatype from a primitive module (such as `Bool` or `Maybe`) can now be
  the target of a compile-to pragma without having a `COMPILE` pragma of its
  own.
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
- The names of type variables in generated Haskell code are now checked to be
  valid Haskell identifiers. Previously an invalid name such as `A` could
  result in invalid Haskell code (see issue #467).
- Type class methods are now imported when they are used in an instance
  declaration, instead of only importing the class itself (see issue #464).
- `if ... then ... else ...` is now parenthesized when it appears as the first
  argument of an infix operator (see issue #460).
- The `zero` and `suc` constructors of `Nat` are now compiled to `0` and
  `succ`, respectively.
- A datatype that is declared before its definition is now compiled correctly
  instead of silently generating no code (see issue #346).
- Using `Set` (or `Type`) as a Haskell type is now rejected with an error.
  This covers both instantiating a type variable with `Set` and datatypes
  indexed by `Set`, which previously produced invalid Haskell (see issues
  #437 and #449).
- The check performed for a `to` pragma now compares the translated Haskell code
  up to alpha-equivalence, so the names of local variables (pattern variables,
  type variables, and lambda, `let`, and `do` bound variables) and of auxiliary
  definitions from a `where` block may differ between the source and the target
  (see issue #479).

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
  The corresponding monad transformer is `MayThrowT`, which compiles to the
  underlying monad. The monad morphism `runMayThrow : MayThrow e a → IO a`
  compiles to `return`. Note that `MayThrow` only makes `throw` sound on the
  Agda side: it does not prevent definitions whose type does not mention
  `MayThrow` from throwing an exception, e.g. by forcing a `MayThrow` value in
  a strict field. The module also provides bindings for the standard Haskell
  exception types, and `MayThrow` and `MayThrowT` have `Functor`,
  `Applicative`, and `Monad` instances. The Prelude provides `IOError`,
  `ioError`, and `userError` for exception handling in `IO`.
- Added `Functor`, `Applicative`, and `Monad` instances for `Delay` in
  `Haskell.Extra.Delay`. Like `MayThrow`, `Delay` is a *transparent* monad:
  it is compiled to the identity monad, so its class methods are compiled to
  their identity counterparts.
- Added bindings to `System.Environment` in `Haskell.System.Environment`
  (see issue #433).
- Added `iDecPair` and `iDecEither` instances to `Haskell.Extra.Dec`, giving
  decidability of pairs and `Either` values from decidability of their
  components.
- Added `Surjection₂` and `MonoidSurjection₂` to `Haskell.Law.Function`,
  together with lemmas for transferring algebraic laws along a surjective
  homomorphism. These are used to derive the `Word` laws from the `Nat` laws.

Changes to the agda2hs Prelude
------------------------------

- The `number`, `numZero`, and `numOne` fields of the `Num` type class have
  been replaced by the `numberFromNum` function and the `zeroOK` and `oneOK`
  fields. The `IsLawfulNum` laws no longer require `FromIntegerOK` arguments
  for `0` and `1`.
- The `∃` type in `Haskell.Extra.Refinement` now has the constructor `_⟨⟩`
  with an implicit proof argument. The old syntax `x ⟨ p ⟩` is still
  available as a pattern synonym.
- The `Word` laws in `Haskell.Law.Num.Word` are now derived from the fact that
  `n2w` is a surjective homomorphism from `Nat` to `Word`. The previous
  postulates that `w2n` preserves addition and multiplication ignored wrapping
  modulo 2⁶⁴ and could be used to prove `⊥` (see issue #499).
- The `Double` definitions of `negate`, `abs` and `signum` in
  `Haskell.Prim.Num`, and of `max` and `min` in `Haskell.Prim.Ord`, now agree
  with GHC's Prelude on signed zeros and NaN (see issue #500).
- Removed the unsound `IsLawfulOrd Double` instance. It was refuted by NaN
  (`NaN <= NaN` and `NaN == NaN` are both `False`) and could be used to prove
  `⊥` (see issue #488).

Changes to agda2hs-containers
-----------------------------

- `prop-member-map` in `Haskell.Data.Set` now states only that
  `member x s ≡ True` implies `member (f x) (map f s) ≡ True`. The previous
  equation does not hold for non-injective `f` and could be used to prove
  `⊥` (see issue #487).

Fixed issues
------------

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.5+is%3Aissue for the full list of fixed issues.
