Release notes for agda2hs v1.4
==============================

Changes
-------

Changes to agda2hs:
- Increased Agda base version to 2.8.
- Increased bounds to support GHC 9.12.2.
- agda2hs will now skip compilation of files that are up-to-date.
- Added support for multi-parameter type classes.
- Added support for quantified constraints.
- Agda record types that compile to a Haskell data type are now
  required to have the `no-eta-equality` directive.
- agda2hs will now assume that any modules under the `Haskell.`
  namespace are part of the trusted FFI with Haskell.
  Concretely, no code will be generated for these modules and
  the `Haskell.` prefix will be dropped from the module name.

Additions to the agda2hs Prelude:
- The builtin sort `Set` has been renamed to `Type` in the agda2hs Prelude
- The `Rezz` type defined in `Haskell.Extra.Erase` has been renamed to `Singleton`.
- The bindings to the Haskell `base` library are now located under `lib/base`
  to allow for adding bindings to other Haskell libraries.
- Added new module `Haskell.Control.Exception` with the `assert` function
  which can be used to assert any decidable property, with the decidability
  proof being compiled to a boolean check in Haskell.
- Added new module `Haskell.Data.Maybe` with `fromMaybe` and other functions.
- Added new module `Haskell.Data.List` with functions `nub`, `deleteAll`, and `sort`
  together with some of their properties.
- Added new modules `Haskell.Data.Map` and `Haskell.Data.Set` from the
  `containers` package, together with a number of their properties.
  These libraries are part of the new `containers` package located in `lib/containers`.
- Added properties of boolean values and operations under `Haskell.Law.Bool`.
- Added laws for the `Num` type class and its instances under `Haskell.Law.Num`.


See https://github.com/agda/agda2hs/issues?q=milestone%3A1.4+is%3Apr for the full list of changes.

Fixed issues
------------

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.4+is%3Aissue for the full list of fixed issues.
