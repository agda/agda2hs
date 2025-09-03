Release notes for agda2hs v1.4
==============================

Changes
-------

Changes to agda2hs:
- Increased Agda base version to 2.8
- Increased bounds to support GHC 9.12.2
- agda2hs will now skip compilation of files that are up-to-date
- Added support for multi-parameter type classes
- Added support for quantified constraints
- Agda record types that compile to a Haskell data type are now
  required to have the `no-eta-equality` directive.

Additions to the agda2hs Prelude:
- Added new module `Haskell.Data.Maybe` with `fromMaybe` and other functions
- Added laws for the Num type class and its instances under `Haskell.Law.Num`
- Added bindings to the Haskell libraries `Data.Map` and `Data.Set` from the
  `containers` package, together with a number of their properties.
  These libraries are part of the new `containers` package located in `lib/containers`.
- The bindings to the Haskell `base` library are now located under `lib/base`.
- The `Rezz` type defined in `Haskell.Extra.Erase` has been renamed to `Singleton`.

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.3+is%3Apr for the full list of changes.

Fixed issues
------------

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.3+is%3Aissue for the full list of fixed issues.
