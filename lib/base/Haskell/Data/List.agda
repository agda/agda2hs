module Haskell.Data.List where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Tuple
open import Haskell.Prim.Int
open import Haskell.Prim.Maybe
open import Haskell.Prim.Eq hiding (module Instances)
open import Haskell.Prim.Ord hiding (module Instances)
open import Haskell.Prim.Num hiding (module Instances)

open import Haskell.Prim.List public
open import Haskell.Prim.Eq public
  using () renaming (module Instances to EqInstances)
open import Haskell.Prim.Ord public
  using () renaming (module Instances to OrdInstances)
open import Haskell.Prim.Num public
  using () renaming (module Instances to NumInstances)
open import Haskell.Prim.Foldable public
  using (null; length; foldl; foldl'; foldl1; foldr; foldr1; sum; product; maximum; minimum; elem)
  renaming (module Instances to FoldableInstances)
open import Haskell.Data.Foldable public
  using (concat; concatMap; and; or; any; all; maximumBy; minimumBy; notElem; find)
open import Haskell.Data.Traversable public using (mapAccumL; mapAccumR)
open import Haskell.Data.String public using (lines; words; unlines; unwords)


variable i : Type

uncons : List a → Maybe (a × List a)
uncons []       = Nothing
uncons (x ∷ xs) = Just (x , xs)

unsnoc : List a → Maybe (List a × a)
unsnoc = foldr (λ x → Just ∘ maybe ([] , x) (λ (a , b) → x ∷ a , b)) Nothing

singleton : a → List a
singleton = _∷ []

compareLength : List a → Int → Ordering
compareLength xs n =
  if n < 0 then GT
  else foldr (λ _ f m → if m > 0 then f (m - 1) else GT) (λ m → if m > 0 then LT else EQ) xs n

foldl1' : (a → a → a) → (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → a
foldl1' f (x ∷ xs) = foldl f x xs

scanl : (b → a → b) → b → List a → List b
scanl f z []       = z ∷ []
scanl f z (x ∷ xs) = z ∷ scanl f (f z x) xs

scanl' : (b → a → b) → b → List a → List b
scanl' = scanl

scanl1 : (a → a → a) → List a → List a
scanl1 f []       = []
scanl1 f (x ∷ xs) = scanl f x xs

scanr : (a → b → b) → b → List a → List b
scanr f z [] = z ∷ []
scanr f z (x ∷ xs) = case scanr f z xs of λ where
  []         → [] -- impossible
  qs@(q ∷ _) → f x q ∷ qs

scanr1 : (a → a → a) → List a → List a
scanr1 f []       = []
scanr1 f (x ∷ xs) = case scanr1 f xs of λ where
  []         → x ∷ []
  qs@(q ∷ _) → f x q ∷ qs

replicateNat : Nat → a → List a
replicateNat zero    _ = []
replicateNat (suc n) x = x ∷ replicateNat n x

replicate : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → a → List a
replicate n = replicateNat (intToNat n)

takeNat : Nat → List a → List a
takeNat n       [] = []
takeNat zero    xs = []
takeNat (suc n) (x ∷ xs) = x ∷ takeNat n xs

take : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → List a → List a
take n xs = takeNat (intToNat n) xs

dropNat : Nat → List a → List a
dropNat n       [] = []
dropNat zero    xs = xs
dropNat (suc n) (_ ∷ xs) = dropNat n xs

drop : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → List a → List a
drop n xs = dropNat (intToNat n) xs

splitAtNat : (n : Nat) → List a → List a × List a
splitAtNat _       []       = [] , []
splitAtNat 0       xs       = [] , xs
splitAtNat (suc n) (x ∷ xs) = first (x ∷_) (splitAtNat n xs)

splitAt : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → List a → List a × List a
splitAt n xs = splitAtNat (intToNat n) xs

takeWhile : (a → Bool) → List a → List a
takeWhile p [] = []
takeWhile p (x ∷ xs) = if p x then x ∷ takeWhile p xs else []

dropWhile : (a → Bool) → List a → List a
dropWhile p [] = []
dropWhile p (x ∷ xs) = if p x then dropWhile p xs else x ∷ xs

dropWhileEnd : (a → Bool) → List a → List a
dropWhileEnd p = foldr (λ x xs → if p x && null xs then [] else x ∷ xs) []

span : (a → Bool) → List a → List a × List a
span p [] = [] , []
span p (x ∷ xs) = if p x then first (x ∷_) (span p xs)
                         else ([] , x ∷ xs)

break : (a → Bool) → List a → List a × List a
break p = span (not ∘ p)

stripPrefix : ⦃ Eq a ⦄ → List a → List a → Maybe (List a)
stripPrefix []       ys       = Just ys
stripPrefix _        []       = Nothing
stripPrefix (x ∷ xs) (y ∷ ys) = if x == y then stripPrefix xs ys else Nothing

reverse : List a → List a
reverse = foldl (flip _∷_) []

inits : List a → List (List a)
inits = map reverse ∘ scanl (flip _∷_) []

tails : List a → List (List a)
tails []           = singleton []
tails xs@(_ ∷ xs') = xs ∷ tails xs'

isPrefixOf : ⦃ Eq a ⦄ → List a → List a → Bool
isPrefixOf []       _        = True
isPrefixOf _        []       = False
isPrefixOf (x ∷ xs) (y ∷ ys) = x == y && isPrefixOf xs ys

isSuffixOf : ⦃ Eq a ⦄ → List a → List a → Bool
isSuffixOf xs ys = isPrefixOf (reverse xs) (reverse ys)

isInfixOf : ⦃ Eq a ⦄ → List a → List a → Bool
isInfixOf xs ys = any (isPrefixOf xs) (tails ys)

isSubsequenceOf : ⦃ Eq a ⦄ → List a → List a → Bool
isSubsequenceOf []           _        = True
isSubsequenceOf _            []       = False
isSubsequenceOf xs@(x ∷ xs') (y ∷ ys) = if x == y then isSubsequenceOf xs' ys
                                        else isSubsequenceOf xs ys

lookup : ⦃ Eq a ⦄ → a → List (a × b) → Maybe b
lookup _ []              = Nothing
lookup k ((x , y) ∷ xys) = if k == x then Just y else lookup k xys

filter : (a → Bool) → List a → List a
filter p []       = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

partition : (a → Bool) → List a → (List a × List a)
partition p xs = (filter p xs , filter (not ∘ p) xs)

infixl 9 _!?_
_!?_ : List a → Int → Maybe a
[]       !? _ = Nothing
(x ∷ xs) !? n = case compare n 0 of λ where
  LT → Nothing
  EQ → Just x
  GT → xs !? (n - 1)

infixl 9 _!!ᴺ_
_!!ᴺ_ : (xs : List a) (n : Nat) → @0 ⦃ IsTrue (n < lengthNat xs) ⦄ → a
(x ∷ xs) !!ᴺ zero  = x
(x ∷ xs) !!ᴺ suc n = xs !!ᴺ n

infixl 9 _!!_
_!!_ : (xs : List a) (n : Int)
     → ⦃ @0 _ : IsNonNegativeInt n ⦄
     → ⦃ @0 _  : IsTrue (intToNat n < lengthNat xs) ⦄ → a
xs !! n = xs !!ᴺ intToNat n

findIndices : (a → Bool) → List a → List Int
findIndices p xs = let go x r k = if p x then k ∷ r (k + 1) else r (k + 1)
                   in foldr go (const []) xs 0

findIndex : (a → Bool) → List a → Maybe Int
findIndex p xs = case findIndices p xs of λ where
  []      → Nothing
  (x ∷ _) → Just x

elemIndices : ⦃ Eq a ⦄ → a → List a → List Int
elemIndices x = findIndices (x ==_)

elemIndex : ⦃ Eq a ⦄ → a → List a → Maybe Int
elemIndex x = findIndex (x ==_)

zipWith : (a → b → c) → List a → List b → List c
zipWith f []       _        = []
zipWith f _        []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

zipWith3 : (a → b → c → d) → List a → List b → List c → List d
zipWith3 f []       _        _        = []
zipWith3 f _        []       _        = []
zipWith3 f _        _        []       = []
zipWith3 f (x ∷ xs) (y ∷ ys) (z ∷ zs) = f x y z ∷ zipWith3 f xs ys zs

zip : List a → List b → List (a × b)
zip = zipWith _,_

zip3 : List a → List b → List c → List (a × b × c)
zip3 = zipWith3 _,_,_

unzip : List (a × b) → List a × List b
unzip []              = [] , []
unzip ((x , y) ∷ xys) = (x ∷_) *** (y ∷_) $ unzip xys

unzip3 : List (a × b × c) → List a × List b × List c
unzip3 []                   = [] , [] , []
unzip3 ((x , y , z) ∷ xyzs) = case unzip3 xyzs of λ where
  (xs , ys , zs) → x ∷ xs , y ∷ ys , z ∷ zs

intersperse : a → List a → List a
intersperse _   []       = []
intersperse sep (x ∷ xs) = x ∷ prependToAll sep xs
  where
    prependToAll : a → List a → List a
    prependToAll _   []       = []
    prependToAll sep (x ∷ xs) = sep ∷ x ∷ prependToAll sep xs

intercalate : List a → List (List a) → List a
intercalate xs xss = concat (intersperse xs xss)

subsequences : List a → List (List a)
subsequences xs = [] ∷ nonEmptySubsequences xs
  where
    nonEmptySubsequences : List a → List (List a)
    nonEmptySubsequences []       = []
    nonEmptySubsequences (x ∷ xs) = let f ys r = ys ∷ (x ∷ ys) ∷ r
                                    in singleton x ∷ foldr f [] (nonEmptySubsequences xs)

nubBy : (a → a → Bool) → List a → List a
nubBy eq [] = []
nubBy eq (x ∷ xs) = x ∷ filter (not ∘ eq x) (nubBy eq xs)

nub : ⦃ Eq a ⦄ → List a → List a
nub = nubBy _==_

deleteBy : (a → a → Bool) → a → List a → List a
deleteBy _  _ []       = []
deleteBy eq x (x' ∷ xs) = if eq x x' then xs else x' ∷ deleteBy eq x xs

delete : ⦃ Eq a ⦄ → a → List a → List a
delete = deleteBy _==_

deleteFirstsBy : (a → a → Bool) → List a → List a → List a
deleteFirstsBy eq = foldl (flip (deleteBy eq))

infix 5 _\\_
_\\_ : ⦃ Eq a ⦄ → List a → List a → List a
_\\_ = deleteFirstsBy _==_

unionBy : (a → a → Bool) → List a → List a → List a
unionBy eq xs ys = xs ++ deleteFirstsBy eq (nubBy eq ys) xs

union : ⦃ Eq a ⦄ → List a → List a → List a
union = unionBy _==_

intersectBy : (a → a → Bool) → List a → List a → List a
intersectBy eq xs ys = filter (λ x → any (eq x) ys) xs

intersect : ⦃ Eq a ⦄ → List a → List a → List a
intersect = intersectBy _==_

insertBy : (a → a → Ordering) → a → List a → List a
insertBy _   x []           = singleton x
insertBy cmp x ys@(y ∷ ys') = case cmp x y of λ where
  GT → y ∷ insertBy cmp x ys'
  _  → x ∷ ys

insert : ⦃ Ord a ⦄ → a → List a → List a
insert = insertBy compare


-- Omitted for now:
-- [obviously non-terminating]
-- - 'iterate :: (a -> a) -> a -> [a]'
-- - 'iterate' :: (a -> a) -> a -> [a]'
-- - 'repeat :: a -> [a]'
-- - 'cycle :: [a] -> [a]'
-- - 'unfoldr :: (b -> Maybe (a, b)) -> b -> [a]

-- [hard to prove termination]
-- - 'groupBy :: (a -> a -> Bool) -> [a] -> [[a]]'
-- - 'group :: Eq a => [a] -> [[a]]'
-- - 'transpose :: [[a]] -> [[a]]'
-- - 'permutations :: [a] -> [[a]]'
-- - 'sortBy :: (a -> a -> Ordering) -> [a] -> [a]'
-- - 'sort :: Ord a => [a] -> [a]'
-- - 'sortOn :: Ord b => (a -> b) -> [a] -> [a]

-- [type signature includes currently not supported (?) `NonEmpty` type]
-- - 'inits1 :: [a] -> [NonEmpty a]'
-- - 'tails1 :: [a] -> [NonEmpty a]'

-- - 'zipWith4', 'zipWith5', 'zipWith6', 'zipWith7'
-- - 'zip4', 'zip5', 'zip6', 'zip7'
-- - 'unzip4', 'unzip5', 'unzip6', 'unzip7'

-- - 'genericLength :: Num i => [a] -> i'
-- - 'genericTake :: Integral i => i -> [a] -> [a]'
-- - 'genericDrop :: Integral i => i -> [a] -> [a]'
-- - 'genericSplitAt :: Integral i => i -> [a] -> ([a], [a])'
-- - 'genericIndex :: Integral i => [a] -> i -> a'
-- - 'genericReplicate :: Integral i => i -> a -> [a]'
