{-# FOREIGN AGDA2HS
-- ** qualifying the Prelude
#-}
import Haskell.Prelude as Pre

_+_ : Pre.Nat → Pre.Nat → Pre.Nat
x + y = x
{-# COMPILE AGDA2HS _+_ #-}

comp : (Pre.Nat → Pre.Nat) → (Pre.Nat → Pre.Nat) → (Pre.Nat → Pre.Nat)
comp f g = f Pre.∘ g
{-# COMPILE AGDA2HS comp #-}

test : Pre.Nat
test = 0 Pre.+ 1 + 0
{-# COMPILE AGDA2HS test #-}

testComp : Pre.Nat
testComp = comp (_+ 0) (Pre._+ 1) 0
{-# COMPILE AGDA2HS testComp #-}

{-# FOREIGN AGDA2HS
-- ** interplay with (qualified) default methods of existing class
#-}

testFoldr : Pre.List Pre.Nat → Pre.Nat
testFoldr = Pre.foldr (λ _ x → x) 0
{-# COMPILE AGDA2HS testFoldr #-}

{-# FOREIGN AGDA2HS
-- ** re-qualifying the Prelude
#-}
import Haskell.Prelude as pre

retest : pre.Nat
retest = 0 pre.+ 1 + 0
{-# COMPILE AGDA2HS retest #-}
