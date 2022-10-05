
open import Haskell.Prelude

data Unit : Set where
  unit : Unit

myId : @0 Unit → a → a
myId unit x = x

{-# COMPILE AGDA2HS myId transparent #-}

testMyId : @0 Unit → Nat
testMyId u = myId u 42

{-# COMPILE AGDA2HS testMyId #-}

tyId : @0 Unit → Set → Set
tyId unit a = a

{-# COMPILE AGDA2HS tyId transparent #-}

testTyId : ∀ {@0 u : Unit} → tyId u (tyId u Int → tyId u Int)
testTyId {unit} n = n

{-# COMPILE AGDA2HS testTyId #-}

data Tree : Set where
  Tip : Tree
  Bin : Tree → Tree → Tree

{-# COMPILE AGDA2HS Tree #-}

treeId : Tree → Tree
treeId Tip = Tip
treeId (Bin x y) = Bin (treeId x) (treeId y)

{-# COMPILE AGDA2HS treeId transparent #-}

testTreeId : Tree → Tree
testTreeId = treeId

{-# COMPILE AGDA2HS testTreeId #-}
