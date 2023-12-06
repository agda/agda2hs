
module Tuples where

open import Haskell.Prelude

swap : a × b → b × a
swap (a , b) = b , a

{-# COMPILE AGDA2HS swap #-}

data TuplePos : Set where
  Test : TuplePos × Bool → TuplePos

{-# COMPILE AGDA2HS TuplePos #-}


t1 : Bool × Bool × Bool
t1 = True , False , True

{-# COMPILE AGDA2HS t1 #-}

t2 : (Bool × Bool) × Bool
t2 = (True , False) , True

{-# COMPILE AGDA2HS t2 #-}

t3 : Bool × (Bool × Bool)
t3 = True , (False , True)

{-# COMPILE AGDA2HS t3 #-}

pair : Int × Int
pair = 1 , 2

{-# COMPILE AGDA2HS pair #-}

test : Int
test = let (x , y) = pair in x + y

{-# COMPILE AGDA2HS test #-}

test2 : Bool
test2 = case t1 of \where
  (a , b , c) → c

{-# COMPILE AGDA2HS test2 #-}

