module TypeSynonyms where

data Nat = Zero
         | Suc Nat

type Nat' = Nat

data List a = Nil
            | Cons a (List a)

type List' a = List a

type NatList = List Nat

type ListList a = List (List a)

