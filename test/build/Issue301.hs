module Issue301 where

data MyData a = Nuttin'

instance Foldable MyData where
    foldMap _ _ = mempty

(><) :: MyData a -> MyData a -> MyData a
_ >< _ = Nuttin'

instance Semigroup (MyData a) where
    (<>) = (><)

instance Monoid (MyData a) where
    mempty = Nuttin'

