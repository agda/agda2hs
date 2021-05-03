[![GitHub CI](https://github.com/agda/agda2hs/workflows/CI/badge.svg)](https://github.com/agda/agda2hs/actions)

## agda2hs

The goal of this project is *not* to translate Agda code to Haskell.
Rather it is to carve out a common sublanguage between Agda and Haskell,
with a straightforward translation from the Agda side to the Haskell side.
This lets you write your program in the Agda fragment, using full Agda
to prove properties about it, and then translate it to nice looking readable
Haskell code that you can show your Haskell colleagues without shame.

See `test/Test.agda` for an example.

### Future work


- [x] Compile lambdas [#5](https://github.com/agda/agda2hs/pull/5)
- [x] Sections [#21](https://github.com/agda/agda2hs/pull/21)
- [x] Compile if/then/else [#13](https://github.com/agda/agda2hs/pull/13)
- [ ] Literals in patterns
- [x] Use some Haskell syntax ADT and a proper pretty printing library [#4](https://github.com/agda/agda2hs/pull/4)
- [x] Map instance arguments to Haskell type classes (definitions and use) [#3](https://github.com/agda/agda2hs/pull/3)
- [x] `where` clauses [#23](https://github.com/agda/agda2hs/pull/23)
- [ ] Higher-rank polymorphism
- [x] More builtin types (Double, Word64) [#12](https://github.com/agda/agda2hs/pull/12)
- [x] Strings
- [ ] Compile `case_of_ λ where` to Haskell `case`
- [ ] `with`?
- [ ] Compile equality proofs to QuickCheck properties?
- [ ] Module export lists (how?)
- [ ] Fixity declarations
