module TypeSynonyms where

data Nat = Zero
         | Suc Nat

type Nat' = Nat

myNat :: Nat'
myNat = Suc (Suc Zero)

data List a = Nil
            | Cons a (List a)

type List' a = List a

type NatList = List Nat

myListFun :: List' Nat' -> NatList
myListFun Nil = Nil
myListFun (Cons x xs) = Cons x (myListFun xs)

type ListList a = List (List a)

flatten :: ListList a -> List a
flatten Nil = Nil
flatten (Cons Nil xss) = flatten xss
flatten (Cons (Cons x xs) xss) = Cons x (flatten (Cons xs xss))

