## agda2hs

Compiles a subset of Agda to readable Haskell code. See Test.agda for an example.

### Future work

- Compile lambdas
- Literals in patterns
- Use some Haskell syntax ADT and a proper pretty printing library
- Map instance arguments to Haskell type classes (definitions and use)
- `where` clauses
- Higher-rank polymorphism
- More builtin types (`Double`, `Word64`)
- Strings (compile to `Data.Text`)
- Compile `case_of_ λ where` to Haskell `case`
- `with`?

