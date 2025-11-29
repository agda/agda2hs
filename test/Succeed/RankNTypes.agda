{-# FOREIGN AGDA2HS
{-# LANGUAGE Haskell98 #-}
#-}

open import Haskell.Prim using (Type)

data MyBool : Type where
    MyTrue : MyBool
    MyFalse : MyBool
{-# COMPILE AGDA2HS MyBool #-}

rank2ForallUse : (∀ (a : Type) → a → a) → MyBool
rank2ForallUse f = f MyBool MyTrue
{-# COMPILE AGDA2HS rank2ForallUse #-}

module _  (f : ∀ (a : Type) → a → a) where
    rank2Module : MyBool
    rank2Module = f MyBool MyTrue
    {-# COMPILE AGDA2HS rank2Module #-}

-- ExistentialQuantification: Not supported yet, but also no error message yet
-- data Exist : Type₁ where
--     MkExist : ∀ (a : Type) → a → Exist
-- {-# COMPILE AGDA2HS Exist #-}
