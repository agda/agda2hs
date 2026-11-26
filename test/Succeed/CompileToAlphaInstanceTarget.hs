module CompileToAlphaInstanceTarget
  (MyList(..))
where

data MyList a = Nil
              | Cons a (MyList a)

instance (Eq a) => Eq (MyList a) where
    (==) = eqMyList
      where
        eqMyList :: MyList a -> MyList a -> Bool
        eqMyList Nil Nil = True
        eqMyList (Cons x xs) (Cons y ys) = x == y && eqMyList xs ys
        eqMyList _ _ = False

