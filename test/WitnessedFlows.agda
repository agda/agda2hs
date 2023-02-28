open import Haskell.Prelude

data Range : Set where
    MkRange : (low high : Int)
            → {{ @0 h : ((low <= high) ≡ True) }}
            → Range

{-# COMPILE AGDA2HS Range #-}

createRange : Int → Int → Maybe Range
createRange low high = if' low <= high then Just (MkRange low high) else Nothing

{-# COMPILE AGDA2HS createRange #-}

createRangeCase : Int → Int → Maybe Range
createRangeCase low high = 
    case' low <= high of λ where
        True → Just (MkRange low high)
        False → Nothing

{-# COMPILE AGDA2HS createRangeCase #-}
