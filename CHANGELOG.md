Release notes for agda2hs v1.5
==============================

Changes to agda2hs
------------------

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
