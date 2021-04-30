module Records where

-- parametrized record type exported as an Haskell record
record Pair (a b : Set) : Set where
  constructor MkPair
  field
    fst : a
    snd : b

{-# COMPILE AGDA2HS Pair #-}

-- record type exported as an Haskell class definition
record MyMonoid (a : Set) : Set where
  field
    mempty  : a
    mappend : a → a → a

{-# COMPILE AGDA2HS MyMonoid class #-}
