record Pointed (a : Set) : Set where
  field
    it : a
open Pointed {{...}} public
{-# COMPILE AGDA2HS Pointed class #-}

data A : Set where A1 : A
{-# COMPILE AGDA2HS A #-}

instance
  iPointedA : Pointed A
  iPointedA .it = A1
{-# COMPILE AGDA2HS iPointedA #-}

data Delay (a : Set) : Set where
  Later : Delay a → Delay a
  Now : a → Delay a
{-# COMPILE AGDA2HS Delay #-}

test : Delay A
test = Later λ where → Now it
{-# COMPILE AGDA2HS test #-}
