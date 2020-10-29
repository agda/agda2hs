## agda2hs

Compiles a subset of Agda to readable Haskell code. Use case: writing your Haskell code in Agda and have `agda2hs` translate it to Haskell, to let you prove properties about it.

See test/Test.agda for an example.

### Future work

- Literals in patterns
- Map instance arguments to Haskell type classes (definitions and use) [#3](https://github.com/agda/agda2hs/pull/3)
- `where` clauses
- Higher-rank polymorphism
- Strings (compile to `Data.Text`)
- Compile `case_of_ λ where` to Haskell `case`
- `with`?
- Compile equality proofs to QuickCheck properties?
- Module export lists (how?)
- Fixity declarations
