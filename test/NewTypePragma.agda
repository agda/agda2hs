open import Haskell.Prelude using ( Int ; fst ; snd
                                  ; a ; b
                                  ; _×_ ; _≡_
                                  )

-- data newtype
{-# FOREIGN AGDA2HS -- data newtype #-}

data Indexed (a : Set) : Set where
    MkIndexed : Int × a → Indexed a

{-# COMPILE AGDA2HS Indexed newtype #-}

index : Int × a → Indexed a
index = MkIndexed

{-# COMPILE AGDA2HS index #-}

-- data newtype with deriving
{-# FOREIGN AGDA2HS -- data newtype with deriving #-}

data Pair (a b : Set) : Set where
    MkPair : a × b → Pair a b

{-# COMPILE AGDA2HS Pair newtype deriving ( Show, Eq ) #-}

-- record newtype
{-# FOREIGN AGDA2HS -- record newtype #-}

record Identity (a : Set) : Set where
    constructor MkIdentity
    field
        runIdentity : a
open Identity public

{-# COMPILE AGDA2HS Identity newtype #-}

-- record newtype with erased proof
{-# FOREIGN AGDA2HS -- record newtype with erased proof #-}

record Equal (a : Set) : Set where
    constructor MkEqual
    field
        pair : a × a
        @0 proof : (fst pair) ≡ (snd pair)
open Equal public

{-# COMPILE AGDA2HS Equal newtype #-}
