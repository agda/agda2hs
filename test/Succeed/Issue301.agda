
open import Haskell.Prelude
open import Haskell.Prim.Monoid
open import Haskell.Prim.Foldable

data MyData (a : Type) : Type where
  Nuttin' : MyData a
{-# COMPILE AGDA2HS MyData #-}

-- notice this does not occur with other classes such as Foldable
myDataDefaultFoldable : DefaultFoldable MyData
DefaultFoldable.foldMap myDataDefaultFoldable _ _ = mempty

instance
  MyDataFoldable : Foldable MyData
  MyDataFoldable = record {DefaultFoldable myDataDefaultFoldable}
{-# COMPILE AGDA2HS MyDataFoldable #-}

-- need to create instance for semigroup first
-- (requires explicitly typed function AFAICT)
_><_ : {a : Type} -> MyData a -> MyData a -> MyData a
_ >< _ = Nuttin'
{-# COMPILE AGDA2HS _><_ #-}

instance
  MyDataSemigroup : Semigroup (MyData a)
  MyDataSemigroup ._<>_ = _><_
{-# COMPILE AGDA2HS MyDataSemigroup #-}

instance
  myDataDefaultMonoid : DefaultMonoid (MyData a)
  DefaultMonoid.mempty myDataDefaultMonoid = Nuttin'

instance
  MyDataMonoid : Monoid (MyData a)
  MyDataMonoid = record {DefaultMonoid myDataDefaultMonoid}
{-# COMPILE AGDA2HS MyDataMonoid #-}
