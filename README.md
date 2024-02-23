[![GitHub CI](https://github.com/agda/agda2hs/workflows/CI/badge.svg)](https://github.com/agda/agda2hs/actions)

# agda2hs

Agda2hs is a tool for producing verified and readable Haskell code by extracting
it from a (lightly annotated) Agda program. The goal of this project is *not* to
translate arbitrary Agda code to Haskell. Rather it is to carve out a common
sublanguage between Agda and Haskell, with a straightforward translation from
the Agda side to the Haskell side. This lets you write your program in the Agda
fragment, using full Agda to prove properties about it, and then translate it to
nice looking readable Haskell code that you can show your Haskell colleagues
without shame.

## Documentation

Documentation can be viewed at https://agda.github.io/agda2hs. You can also find
examples in the `test` directory of this repository, in particular the file
[Test.agda](https://github.com/agda/agda2hs/blob/master/test/Test.agda). The
documentation is a work in progress, so if you have been using agda2hs and want
to contribute in some way, adding documentation or examples would be very
welcome.

agda2hs was introduced in the Haskell Symposium '22 paper [Reasonable Agda is
Correct Haskell: Writing Verified Haskell using
agda2hs](https://jesper.sikanda.be/files/reasonable-agda-is-correct-haskell.pdf).

## Future work

Currently agda2hs is under active development, please take a look at
the [issue tracker](https://github.com/agda/agda2hs/issues). If you
have a suggestion for a new feature that is not yet on the issue
tracker, you are welcome to create a new issue or a PR. Feature
requests should be of the form "Add support for Haskell feature X",
*not* "Add support for Agda feature Y" (see "Objective" above). If you
want to compile arbitrary Agda code to Haskell, you are advised to use
Agda's built-in GHC backend instead.
