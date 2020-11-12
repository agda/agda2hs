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

- [ ] Literals in patterns
- [ ] Map instance arguments to Haskell type classes (definitions and use) [#3](https://github.com/agda/agda2hs/pull/3)
- [ ] `where` clauses
- [ ] Higher-rank polymorphism
- [ ] Strings (compile to `Data.Text`)
- [ ] Compile `case_of_ λ where` to Haskell `case`
- [ ] `with`?
- [ ] Compile equality proofs to QuickCheck properties?
- [ ] Module export lists (how?)
- [ ] Fixity declarations
