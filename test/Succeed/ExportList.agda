
module ExportList where

open import Haskell.Prelude using ( a; Nat; suc; zero; _+_; List; []; _∷_; _≡_; refl )
open import Haskell.Extra.Refinement using ( ∃; _⟨_⟩ )
open import Haskell.Law.Equality using ( cong )

private variable
  @0 n : Nat

-- Function

publicFun : {a : Set} → a → a
publicFun x = x
{-# COMPILE AGDA2HS publicFun #-}

inlineFun : {a : Set} → a → a
inlineFun x = x
{-# COMPILE AGDA2HS inlineFun inline #-}

transparentFun : {a : Set} → a → a
transparentFun x = x
{-# COMPILE AGDA2HS transparentFun transparent #-}

private
  privateFun : {a : Set} → a → a
  privateFun x = x
  {-# COMPILE AGDA2HS privateFun #-}


module M where

  publicFun2 : {a : Set} → a → a
  publicFun2 x = x
  {-# COMPILE AGDA2HS publicFun2 #-}

  private
    privateFun2 : {a : Set} → a → a
    privateFun2 x = x
    {-# COMPILE AGDA2HS privateFun2 #-}


private module M2 where

  privateFun3 : {a : Set} → a → a
  privateFun3 x = x
  {-# COMPILE AGDA2HS privateFun3 #-}

-- Type synonym

PublicTy : Set
PublicTy = Nat
{-# COMPILE AGDA2HS PublicTy #-}

private
  PrivateTy : Set
  PrivateTy = Nat
  {-# COMPILE AGDA2HS PrivateTy #-}

-- Datatype

data PublicData : Set where
  MkPublicData : PublicData
{-# COMPILE AGDA2HS PublicData #-}

private
  data PrivateData : Set where
    MkPrivateData : PrivateData
{-# COMPILE AGDA2HS PrivateData #-}

data PublicNewtype : Set where
  MkPublicNewtype : Nat → PublicNewtype
{-# COMPILE AGDA2HS PublicNewtype newtype #-}

private
  data PrivateNewtype : Set where
    MkPrivateNewtype : Nat → PrivateNewtype
{-# COMPILE AGDA2HS PrivateNewtype newtype #-}

-- Record

record PublicRecord : Set where
  no-eta-equality
  constructor MkPublicRecord
  field publicField : Nat

open PublicRecord public
{-# COMPILE AGDA2HS PublicRecord #-}

record UnboxedRecord : Set where
  no-eta-equality
  constructor MkUnboxedRecord
  field unboxedField : Nat

open UnboxedRecord public
{-# COMPILE AGDA2HS UnboxedRecord unboxed #-}

record TupleRecord : Set where
  no-eta-equality
  constructor MkTupleRecord
  field
    tupleField1 : Nat
    tupleField2 : Nat

open TupleRecord public
{-# COMPILE AGDA2HS TupleRecord tuple #-}

-- Typeclass

record PublicClass : Set where
  field publicMethod : Nat

open PublicClass ⦃ ... ⦄ public
{-# COMPILE AGDA2HS PublicClass class #-}

-- Compile to

data Vec (a : Set) : @0 Nat → Set where
  []  : Vec a 0
  _∷_ : a → Vec a n → Vec a (suc n)
{-# COMPILE AGDA2HS Vec to List #-}

llength : List a → Nat
llength [] = 0
llength (x ∷ xs) = 1 + llength xs
{-# COMPILE AGDA2HS llength #-}

vlength : Vec a n → ∃ Nat (_≡ n)
vlength [] = 0 ⟨ refl ⟩
vlength (x ∷ xs) =
  let n ⟨ eq ⟩ = vlength xs
  in  (1 + n) ⟨ cong suc eq ⟩
{-# COMPILE AGDA2HS vlength to llength #-}
