module ErasedTypeArguments where

data Σ' a b = (:^:){proj₁ :: a, proj₂ :: b}

