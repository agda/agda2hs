open import Haskell.Prelude

data A : Set where
  MkA : Nat → A

data B : Set where
  MkB : Nat → B

postulate A≡B : A ≡ B

coerceExample : B
coerceExample = coerce A≡B (MkA 5)

{-# COMPILE AGDA2HS A newtype #-}
{-# COMPILE AGDA2HS B newtype deriving (Show) #-}
{-# COMPILE AGDA2HS coerceExample #-}
