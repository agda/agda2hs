open import Haskell.Prelude hiding (false; true)

-- A datatype from a primitive module can be the target of a compile-to pragma
-- even though it has no COMPILE pragma of its own.
data MyBool : Set where
  false : MyBool
  true  : MyBool

{-# COMPILE AGDA2HS MyBool to Bool #-}

instance
  iEqMyBool : Eq MyBool
  iEqMyBool ._==_ false false = True
  iEqMyBool ._==_ true  true  = True
  iEqMyBool ._==_ _     _     = False

{-# COMPILE AGDA2HS iEqMyBool to iEqBool #-}

myNot : MyBool → MyBool
myNot false = true
myNot true  = false

{-# COMPILE AGDA2HS myNot #-}
