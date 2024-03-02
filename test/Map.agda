-- A test pack for Data.Map.
module Map where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Ord
open import Haskell.Prim.Tuple
open import Haskell.Law.Equality
import Haskell.Data.Map as Map
open Map using (Map)

firstMap : Map Nat Nat
firstMap = Map.fromList ((50 , 5) ∷ (40 , 4) ∷ (100 , 10) ∷ [])
{-# COMPILE AGDA2HS firstMap #-}

val1 : Maybe Nat
val1 = Map.lookup 100 firstMap
{-# COMPILE AGDA2HS val1 #-}

@0 test1 : val1 ≡ Just 10
test1 = trans (Map.insertNotChangingOthers 100 50 5 (Map.fromList ((40 , 4) ∷ (100 , 10) ∷ [])))
        (trans (Map.insertNotChangingOthers 100 40 4 (Map.fromList ((100 , 10) ∷ [])))
               (Map.memberAfterInsertion 100 10 Map.empty))

val2 : Maybe Nat
val2 = Map.lookup 15 firstMap
{-# COMPILE AGDA2HS val2 #-}

@0 test2 : val2 ≡ Nothing
test2 = trans (Map.insertNotChangingOthers 15 50 5 (Map.fromList ((40 , 4) ∷ (100 , 10) ∷ [])))
        (trans (Map.insertNotChangingOthers 15 40 4 (Map.fromList ((100 , 10) ∷ [])))
        (trans (Map.insertNotChangingOthers 15 100 10 Map.empty)
               (fst (Map.notMember↔Nothing 15 Map.empty)
                      (Map.nullHasNoMembers Map.empty Map.emptyIsNull 15))))

secondMap : Map Nat Nat
secondMap = Map.delete 50 firstMap
{-# COMPILE AGDA2HS secondMap #-}

val3 : Maybe Nat
val3 = Map.lookup 50 secondMap
{-# COMPILE AGDA2HS val3 #-}

@0 test3 : val3 ≡ Nothing
test3 = fst (Map.notMember↔Nothing 50 secondMap)
          (Map.notMemberAfterDeletion 50 firstMap)

val4 : Maybe Nat
val4 = Map.lookup 100 secondMap
{-# COMPILE AGDA2HS val4 #-}

@0 test4 : val4 ≡ Just 10
test4 = trans (Map.deleteNotChangingOthers 100 50 firstMap)
              test1
