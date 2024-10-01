# Introduction

## Getting Started

### Requirements

- [Haskell programming language](https://www.haskell.org)
- [Haskell Cabal](https://www.haskell.org/cabal/)
- [Agda programming language](https://github.com/agda/agda)
  - version >= 2.6.4 && < 2.6.5
- [Agda standard library](https://github.com/agda/agda-stdlib)
- Agda library `agda2hs`
  - this Agda library is included in the `agda2hs` repository; see
    [`agda2hs.agda-lib`](https://github.com/agda/agda2hs/blob/master/agda2hs.agda-lib)
  - you can navigate the library in [HTML format](https://agda.github.io/agda2hs/lib/),
    along with a comprehensive [test suite](https://agda.github.io/agda2hs/test/)

### Installation with Cabal

agda2hs is released [on Hackage](https://hackage.haskell.org/package/agda2hs),
and can be installed with Cabal:

```sh
cabal install agda2hs
```

Once installed, the agda2hs prelude bundled with agda2hs
can be registered in the Agda config using the `agda2hs locate` command:

```sh
agda2hs locate >> ~/.agda/libaries
```

Optionally, the agda2hs prelude can also be added as a default global import:

```sh
echo agda2hs >> ~/.agda/defaults
```

### Manual installation

Let `DIR` be the directory in which you start running these shell commands.
```sh
# clone the repository locally
git clone git@github.com:agda/agda2hs.git

# build agda2hs with cabal
cd agda2hs
cabal install

# register the agda2hs Agda library
echo $(pwd)/agda2hs.agda-lib >> ~/.agda/libraries
# register the agda2hs Agda library as a default
echo agda2hs >> ~/.agda/defaults
```

### Running `agda2hs`

To run agda2hs, run
```
agda2hs <path>/<name>.agda [-o <outputDir>]
```
which, for all dependencies of that Agda file, compiles and writes
```
[<outputDir>/]<modulePath>.hs
```

### Using agda2hs with Stack

You can use agda2hs with the [Haskell
Stack](https://docs.haskellstack.org/en/stable/) tool.

TODO: integrate agda2hs as a preprocessor for stack
