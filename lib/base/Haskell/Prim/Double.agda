
module Haskell.Prim.Double where

open import Agda.Builtin.Float public renaming (Float to Double)

open import Haskell.Prim

instance
  iNumberDouble : Number Double
  iNumberDouble .Number.Constraint _ = ⊤
  iNumberDouble .fromNat n = primNatToFloat n

  iNegativeDouble : Negative Double
  iNegativeDouble .Negative.Constraint _ = ⊤
  iNegativeDouble .fromNeg n = primFloatMinus 0.0 (fromNat n)
