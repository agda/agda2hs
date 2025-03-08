open import Haskell.Prelude

record Σ (a : Type) (b : @0 a → Type) : Type where
  constructor _,_
  field
    fst : a
    snd : b fst
open Σ public
{-# COMPILE AGDA2HS Σ tuple #-}

test : Σ Int (λ _ → Int) → Int
test xy = fst xy + snd xy

{-# COMPILE AGDA2HS test #-}

record Stuff (a : Type) : Type where
  no-eta-equality; pattern
  constructor stuff
  field
    something : Int
    more : a
    another : Bool

{-# COMPILE AGDA2HS Stuff unboxed-tuple #-}

foo : Stuff Int → Stuff Bool → Stuff Char
foo (stuff a b c) (stuff x y z) = stuff (a + b + x) 'x' (or (c ∷ y ∷ z ∷ []))

{-# COMPILE AGDA2HS foo #-}

bare : Int → Char → Bool → Stuff Char
bare = stuff

{-# COMPILE AGDA2HS bare #-}

section : a → Bool → Stuff a
section = stuff 42

{-# COMPILE AGDA2HS section #-}

record NoStuff : Type where
  no-eta-equality; pattern
  constructor dontlook

{-# COMPILE AGDA2HS NoStuff tuple #-}

bar : NoStuff → NoStuff
bar dontlook = dontlook

{-# COMPILE AGDA2HS bar #-}

-- This is legal, basically the same as an unboxed record.
record Legal (a : Type) : Type where
  constructor mkLegal
  field
    theA : a

{-# COMPILE AGDA2HS Legal tuple #-}

baz : Legal Int → Legal Int
baz (mkLegal x) = mkLegal 42

{-# COMPILE AGDA2HS baz #-}
