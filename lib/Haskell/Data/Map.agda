-- An incomplete interface of
-- Haskell's Data.Map.
-- See https://hackage.haskell.org/package/containers-0.4.0.0/docs/src/Data-Map.html.

-- We don't actually implement maps;
-- we only postulate an interface
-- and some basic properties.

module Haskell.Data.Map where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat hiding (_<_)
open import Agda.Builtin.Int
open import Agda.Builtin.List
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monoid
open import Haskell.Prim.Ord
open import Haskell.Prim.Tuple
import Haskell.Prim.String
open import Haskell.Prim using (case_of_; _$_; _≡_; if_then_else_; ⊥; IsTrue; IsFalse)
open import Haskell.Prelude using (error)

variable
  k v a b : Set

postulate
  Map : (k a :  Set) -> Set

  iMonoidMap : {k v : Set} {{ordk : Ord k}} -> Monoid (Map k v)

  -- Constructs an empty map.
  empty : Map k a

  -- | /O(1)/. Is the map empty?
  --
  -- > Data.Map.null (empty)           == True
  -- > Data.Map.null (singleton 1 'a') == False
  null : Map k a -> Bool
  @0 emptyIsNull : ∀ {k a : Set} -> IsTrue (null (empty {k} {a}))

  -- | /O(1)/. The number of elements in the map.
  --
  -- > size empty                                   == 0
  -- > size (singleton 1 'a')                       == 1
  -- > size (fromList([(1,'a'), (2,'c'), (3,'b')])) == 3
  size : Map k a -> Nat   -- should we use Nat or Int here?
  @0 nullHasSize0 : ∀ (map : Map k a) -> IsTrue (null map) -> size map ≡ 0

  -- | /O(log n)/. Lookup the value at a key in the map.
  --
  -- The function will return the corresponding value as @('Just' value)@,
  -- or 'Nothing' if the key isn't in the map.
  lookup : {{ordk : Ord k}} -> k -> Map k a -> Maybe a

  -- Same, but returns a tuple with the key and the value.
  lookupAssoc : {{ordk : Ord k}} -> Map k a -> Maybe (k × a)

  -- | /O(log n)/. Is the key a member of the map? See also 'notMember'.
  --
  -- > member 5 (fromList [(5,'a'), (3,'b')]) == True
  -- > member 1 (fromList [(5,'a'), (3,'b')]) == False
  member : {{ordk : Ord k}} -> k -> Map k a -> Bool

notMember : {{ordk : Ord k}} -> k -> Map k a -> Bool
notMember key map = not (member key map)

postulate
  @0 notMember↔Nothing : {{ordk : Ord k}} -> ∀ (key : k) (map : Map k a)
                            -> IsFalse (member key map) ↔ lookup key map ≡ Nothing
  @0 nullHasNoMembers : {{ordk : Ord k}} -> ∀ (map : Map k a) -> IsTrue (null map)
                          -> ∀ (key : k) -> IsFalse (member key map)

  -- | /O(log n)/. Find the value at a key.
  -- Calls 'error' when the element can not be found.
  -- Consider using 'lookup' when elements may not be present.
  find : {{ordk : Ord k}} (key : k) (map : Map k a) -> @0 IsTrue (member key map)
           -> a
  @0 findSameAsLookup : {{ordk : Ord k}} (key : k) (map : Map k a) (@0 isMember : IsTrue (member key map))
                          -> lookup key map ≡ Just (find key map isMember)

-- I think it's easier to write a definition here.
findWithDefault : {{ordk : Ord k}} -> a -> k -> Map k a -> a
findWithDefault def k m = case lookup k m of λ where
    Nothing   -> def
    (Just x)  -> x

postulate
  singleton : k -> a -> Map k a
  @0 singletonHasItsElement : {{ordk : Ord k}} -> ∀ (key : k) (val : a)
                                -> lookup key (singleton key val) ≡ Just val
  
  {--------------------------------------------------------------------
    Insertion
  --------------------------------------------------------------------}
  -- | /O(log n)/. Insert a new key and value in the map.
  -- If the key is already present in the map, the associated value is
  -- replaced with the supplied value. 'insert' is equivalent to
  -- @'insertWith' 'const'@.
  --
  -- > insert 5 'x' (fromList [(5,'a'), (3,'b')]) == fromList [(3, 'b'), (5, 'x')]
  -- > insert 7 'x' (fromList [(5,'a'), (3,'b')]) == fromList [(3, 'b'), (5, 'a'), (7, 'x')]
  -- > insert 5 'x' empty                         == singleton 5 'x'
  insert : {{ordk : Ord k}} -> k -> a -> Map k a -> Map k a
  @0 memberAfterInsertion : {{ordk : Ord k}} -> ∀ (key : k) (val : a) (map : Map k a)
                              -> lookup key (insert key val map) ≡ Just val
  @0 sizeIncreasesAfterInsertion : {{ordk : Ord k}}  -> ∀ (key : k) (val : a) (map : Map k a)
                              -> @0 IsFalse (member key map)
                              -> size (insert key val map) ≡ suc (size map)
  @0 sizeRemainsAfterInsertion : {{ordk : Ord k}}  -> ∀ (key : k) (val : a) (map : Map k a)
                              -> @0 IsTrue (member key map)
                              -> size (insert key val map) ≡ size map

-- | /O(n*log n)/. Build a map from a list of key\/value pairs. See also 'fromAscList'.
-- If the list contains more than one value for the same key, the last value
-- for the key is retained.
fromList : {{ordk : Ord k}} -> List (k × a) -> Map k a
fromList [] = empty
fromList ((key , val) ∷ xs) = insert key val (fromList xs)

postulate
  -- | /O(log n)/. Insert with a function, combining key, new value and old value.
  -- @'insertWithKey' f key value mp@ 
  -- will insert the pair (key, value) into @mp@ if key does
  -- not exist in the map. If the key does exist, the function will
  -- insert the pair @(key,f key new_value old_value)@.
  -- Note that the key passed to f is the same key passed to 'insertWithKey'.
  --
  -- > let f key new_value old_value = (show key) ++ ":" ++ new_value ++ "|" ++ old_value
  -- > insertWithKey f 5 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "5:xxx|a")]
  -- > insertWithKey f 7 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a"), (7, "xxx")]
  -- > insertWithKey f 5 "xxx" empty                         == singleton 5 "xxx"

  insertWithKey : {{ordk : Ord k}} -> (k -> a -> a -> a) -> k -> a -> Map k a -> Map k a
  @0 insertWithKeyIfMember : {{ordk : Ord k}}
                            -> ∀ (f : k -> a -> a -> a) (key : k) (newval : a) (map : Map k a)
                            -> (@0 isMember : IsTrue (member key map))
                            -> insertWithKey f key newval map ≡ insert
                                                                  key
                                                                  (f key newval (find key map isMember))
                                                                  map
  @0 insertWithKeyIfNotMember : {{ordk : Ord k}}
                            -> ∀ (f : k -> a -> a -> a) (key : k) (newval : a) (map : Map k a)
                            -> (@0 isNotMember : IsFalse (member key map))
                            -> insertWithKey f key newval map ≡ insert key newval map

-- | /O(log n)/. Insert with a function, combining new value and old value.
-- @'insertWith' f key value mp@ 
-- will insert the pair (key, value) into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the pair @(key, f new_value old_value)@.
insertWith : {{ordk : Ord k}} -> (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWith f key newval map = insertWithKey (λ _ new old -> f new old) key newval map

-- | /O(log n)/. Combines insert operation with old value retrieval.
-- The expression (@'insertLookupWithKey' f k x map@)
-- is a pair where the first element is equal to (@'lookup' k map@)
-- and the second element equal to (@'insertWithKey' f k x map@).
insertLookupWithKey : {{ordk : Ord k}} -> (k -> a -> a -> a) -> k -> a -> Map k a
                   -> (Maybe a × Map k a)
insertLookupWithKey f key newval map = lookup key map , insertWithKey f key newval map

postulate
  {--------------------------------------------------------------------
    Deletion
    [delete] is the inlined version of [deleteWith (\k x -> Nothing)]
  --------------------------------------------------------------------}
  -- | /O(log n)/. Delete a key and its value from the map. When the key is not
  -- a member of the map, the original map is returned.
  delete : {{ordk : Ord k}} -> k -> Map k a -> Map k a
  @0 notMemberAfterDeletion : {{ordk : Ord k}} -> ∀ (key : k) (map : Map k a)
                                -> IsFalse (member key (delete key map))
  @0 sizeDecreasesAfterDeletion : {{ordk : Ord k}} -> ∀ (key : k) (map : Map k a)
                                -> @0 IsTrue (member key map)
                                -> size map ≡ suc (size (delete key map))
  {- This follows from the next one.
  @0 sizeRemainsAfterDeletion : {{ordk : Ord k}} -> ∀ (key : k) (map : Map k a)
                                -> @0 IsFalse (member key map)
                                -> size map ≡ size (delete key map)
  -}
  @0 deletingWhatThereIsNot : {{ordk : Ord k}} -> ∀ (key : k) (map : Map k a)
                                -> @0 IsFalse (member key map)
                                -> map ≡ delete key map

  @0 insertAndDelete : {{ordk : Ord k}} -> ∀ (key : k) (val : a) (map : Map k a)
                                -> @0 IsFalse (member key map)
                                -> delete key (insert key val map) ≡ map
  @0 deleteAndInsert : {{ordk : Ord k}} -> ∀ (key : k) (map : Map k a)
                                -> (@0 isMember : IsTrue (member key map))
                                -> insert key (find key map isMember) (delete key map)
                                     ≡ map

  @0 insertNotChangingOthers : {{ordk : Ord k}} -> ∀ (key1 key2 : k) (val : a) (map : Map k a)
                                -> lookup key1 (insert key2 val map) ≡ lookup key1 map
  @0 deleteNotChangingOthers : {{ordk : Ord k}} -> ∀ (key1 key2 : k) (map : Map k a)
                                -> lookup key1 (delete key2 map) ≡ lookup key1 map

-- Done until delete.
