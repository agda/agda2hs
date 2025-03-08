# agda2hs Documentation

`agda2hs` is a tool for producing verified and readable Haskell code by
extracting it from a (lightly annotated) Agda program. For example,
the following Agda program encodes well-formed binary search trees:

```agda
open import Haskell.Prelude

_≤_ : {{Ord a}} → a → a → Type
x ≤ y = (x <= y) ≡ True

data BST (a : Type) {{@0 _ : Ord a}} (@0 lower upper : a) : Type where
  Leaf : (@0 pf : lower ≤ upper) → BST a lower upper
  Node : (x : a) (l : BST a lower x) (r : BST a x upper) → BST a lower upper

{-# COMPILE AGDA2HS BST #-}
```

agda2hs translates this to the following Haskell datatype:

```haskell
module BST where

data BST a = Leaf
           | Node a (BST a) (BST a)
```

`agda2hs` is intended to be used together with the provided `Haskell.Prelude`
module, which provides an Agda implementation of (a large subset of) the Haskell
Prelude. It also provides proofs for reasoning about Haskell functions under the
`Haskell.Law` namespace. `agda2hs` is *not* compatible with other Agda libraries
such as the Agda standard library.

## Objective

The goal of this project is *not* to translate arbitrary Agda code to Haskell.
Rather it is to carve out a common sublanguage between Agda and Haskell,
with a straightforward translation from the Agda side to the Haskell side.
This lets you write your program in the Agda fragment, using full Agda
to prove properties about it, and then translate it to nice looking readable
Haskell code that you can show your Haskell colleagues without shame.

If you want to compile arbitrary Agda programs to runnable (but not readable)
Haskell, you should instead use the built-in
[GHC backend of Agda](https://agda.readthedocs.io/en/v2.6.4/tools/compilers.html#ghc-backend)
(a.k.a. MAlonzo).

## Documentation

The documentation you are currently reading is a work in progress, so if you
have been using `agda2hs` and want to contribute in some way, adding
documentation or examples would be very welcome.

agda2hs was introduced in the Haskell Symposium '22 paper [Reasonable Agda is
Correct Haskell: Writing Verified Haskell using
agda2hs](https://jesper.sikanda.be/files/reasonable-agda-is-correct-haskell.pdf).

## Future work

Currently `agda2hs` is under active development, please take a look at the
[issue tracker](https://github.com/agda/agda2hs/issues). If you have a
suggestion for a new feature that is not yet on the issue tracker, you are
welcome to create a new issue or a PR. Feature requests should be of the form
"Add support for Haskell feature X", *not* "Add support for Agda feature Y" (see
"Objective" above). If you want to compile arbitrary Agda code to Haskell, you
are advised to use Agda's built-in GHC backend instead.


```{toctree}
---
maxdepth: 1
caption: Contents
---
introduction
features
tutorials
```
