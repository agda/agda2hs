Release notes for agda2hs v1.2
==============================

Changes
-------

- Increased bounds to support GHC 9.6.3
- Changed flag `--rewrite-rules` to `--config`.
- Deprecated `Tuple` (#228). Now there are distinct 2-uples (`_×_`) and 3-uples (`_×_×_`).
  Only 2-uples can be pattern-matched inside of let bindings.
- Experimental support for *erased module parameters* (#229).
- Support for erased hidden type parameters.
- Functions with no clause throw a hard error when getting compiled.
- Unboxed records can preserve any field -- not only the first one.
- Improved documentation.

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.2+is%3Apr for the full list of changes.

Fixed issues
------------

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.2+is%3Aissue for the full list of fixed issues.
