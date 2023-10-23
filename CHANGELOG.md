Release notes for agda2hs v1.1
==============================

Changes
-------

- Updated Agda base version to 2.6.4.
- The `agda2hs` executable can now also be used in interactive mode (e.g. in Emacs or VS Code).
- Added option to specify user-defined rewrites (see https://agda.github.io/agda2hs/features.html#rewrite-rules).
- Type operators with names not starting with a colon are now allowed.
- Added bindings for the `IO` monad.
- Various other additions to the `Haskell.Prelude` library.

Fixed issues
------------

See https://github.com/agda/agda2hs/issues?q=milestone%3A1.1+is%3Aissue for the full list of fixed issues.