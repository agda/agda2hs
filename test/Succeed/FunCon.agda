
open import Haskell.Prelude

data D1 (t : Type → Type) : Type where
  C1 : t Bool → D1 t

{-# COMPILE AGDA2HS D1 #-}

f1 : D1 (λ a → Int → a)
f1 = C1 (_== 0)

{-# COMPILE AGDA2HS f1 #-}

data D2 (t : Type → Type → Type) : Type where
  C2 : t Int Int → D2 t

{-# COMPILE AGDA2HS D2 #-}

f2 : D2 (λ a b → a → b)
f2 = C2 (_+ 1)

{-# COMPILE AGDA2HS f2 #-}
