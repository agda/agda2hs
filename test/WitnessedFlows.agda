open import Haskell.Prelude
open import Haskell.Control.Monad

data Range : Set where
    MkRange : (low high : Int)
            → {{ @0 h : ((low <= high) ≡ True) }}
            → Range

{-# COMPILE AGDA2HS Range #-}

createRange : Int → Int → Maybe Range
createRange low high = if low <= high then Just (MkRange low high) else Nothing

{-# COMPILE AGDA2HS createRange #-}

createRange' : Int → Int → Maybe Range
createRange' low high =
    if low <= high then
        (λ {{ h }} → if low <= high then Just (MkRange low high {{ h }}) else Nothing)
    else Nothing

{-# COMPILE AGDA2HS createRange' #-}

createRangeCase : Int → Int → Maybe Range
createRangeCase low high =
    case low <= high of λ where
        True → Just (MkRange low high)
        False → Nothing

{-# COMPILE AGDA2HS createRangeCase #-}

createRangeGuardSeq : Int → Int → Maybe Range
createRangeGuardSeq low high =
  do guard (low <= high)
     pure (MkRange low high)

{-# COMPILE AGDA2HS createRangeGuardSeq #-}

createRangeGuardFmap : Int → Int → Maybe Range
createRangeGuardFmap low high
  = MkRange low high <$ guard (low <= high)

{-# COMPILE AGDA2HS createRangeGuardFmap #-}
