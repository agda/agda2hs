open import Haskell.Prim using (Type)
open import Haskell.Prelude using ( Int ; fst ; snd
                                  ; a ; b
                                  ; _×_ ; _,_
                                  ; _≡_; refl
                                  ; List; map
                                  )

{-# FOREIGN AGDA2HS
-- data newtype
#-}

data Indexed (a : Type) : Type where
    MkIndexed : Int × a → Indexed a

{-# COMPILE AGDA2HS Indexed newtype #-}

index : Int × a → Indexed a
index = MkIndexed

{-# COMPILE AGDA2HS index #-}

{-# FOREIGN AGDA2HS
-- data newtype with deriving
#-}

data Pair (a b : Type) : Type where
    MkPair : a × b → Pair a b

{-# COMPILE AGDA2HS Pair newtype deriving ( Show, Eq ) #-}

{-# FOREIGN AGDA2HS
-- record newtype
#-}

record Identity (a : Type) : Type where
    no-eta-equality
    constructor MkIdentity
    field
        runIdentity : a
open Identity public

{-# COMPILE AGDA2HS Identity newtype #-}

{-# FOREIGN AGDA2HS
-- record newtype with erased proof
#-}

record Equal (a : Type) : Type where
    no-eta-equality
    constructor MkEqual
    field
        pair : a × a
        @0 proof : fst pair ≡ snd pair
open Equal public

{-# COMPILE AGDA2HS Equal newtype #-}

{-# FOREIGN AGDA2HS
-- record newtype with same name
#-}

record Duo (a : Type) : Type where
    no-eta-equality
    field
        duo : a × a
open Duo public

{-# COMPILE AGDA2HS Duo newtype #-}

createDuo : a → a → Duo a
createDuo a b = record { duo = a , b }

{-# COMPILE AGDA2HS createDuo #-}
