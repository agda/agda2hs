{-# FOREIGN AGDA2HS
{-# LANGUAGE Haskell98 #-}
#-}

data MyBool : Set where
    MyTrue : MyBool
    MyFalse : MyBool
{-# COMPILE AGDA2HS MyBool #-}

rank2ForallUse : (∀ (a : Set) → a → a) → MyBool
rank2ForallUse f = f MyBool MyTrue
{-# COMPILE AGDA2HS rank2ForallUse #-}

module _  (f : ∀ (a : Set) → a → a) where
    rank2Module : MyBool
    rank2Module = f MyBool MyTrue
    {-# COMPILE AGDA2HS rank2Module #-}

-- ExistentialQuantification: Not supported yet, but also no error message yet
-- data Exist : Set₁ where
--     MkExist : ∀ (a : Set) → a → Exist
-- {-# COMPILE AGDA2HS Exist #-}
