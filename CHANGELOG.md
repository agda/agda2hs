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
- Postulates in a `where` block are now compiled to a runtime error instead of
  crashing the compiler. Declarations other than functions and postulates are
  rejected with a proper error message (see issue #443).
- The `Traversable` instances in the Prelude are now defined directly using
  copatterns and default instances instead of the `traverse=` helper, so that
  they pass the instance validity check (see issue #457).

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.5+is%3Apr for the full list of changes.

Additions to the agda2hs Prelude
--------------------------------

- Added `predNat` to `Haskell.Extra.Nat`: the predecessor of a nonzero
  natural number, returning the predecessor together with a proof that
  the original number is its successor. It compiles to Haskell's `pred`
  and enables defining functions such as a `Nat` recursor on top of
  `ifDec` (see issue #385).

Fixed issues
------------

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.5+is%3Aissue for the full list of fixed issues.
