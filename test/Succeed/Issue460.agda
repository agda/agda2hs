open import Haskell.Prelude

prepend : Bool → List Int → List Int
prepend b xs = (if b then 1 ∷ [] else []) ++ xs

{-# COMPILE AGDA2HS prepend #-}
