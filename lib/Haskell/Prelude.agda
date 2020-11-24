{-# OPTIONS --no-auto-inline #-}
module Haskell.Prelude where

open import Agda.Builtin.Unit         public
open import Agda.Builtin.Nat as Nat   public hiding (_==_; _<_)
open import Agda.Builtin.List         public
open import Agda.Builtin.Bool         public
open import Agda.Builtin.Float        public
open import Agda.Builtin.Char         public
open import Agda.Builtin.FromString   public
import Agda.Builtin.String as Str
open import Agda.Builtin.Strict
open import Agda.Builtin.FromNat      public using (fromNat)
open import Agda.Builtin.FromNeg      public using (fromNeg)

open import Haskell.Prim
open Haskell.Prim public using (if_then_else_; iNumberNat)

open import Haskell.Prim.Integer
open Haskell.Prim.Integer public using (Integer; iNumberInteger; iNegativeInteger)

open import Haskell.Prim.Int renaming (Int64 to Int)
open Haskell.Prim.Int public using (iNumberInt; iNegativeInt) renaming (Int64 to Int)

open import Haskell.Prim.Word

-- Problematic features
--  - [Partial]:  Could pass implicit/instance arguments to prove totality.
--  - [Int]:      Agda doesn't have Int64. What to do?
--  - [Float]:    Or Float (Agda floats are Doubles)
--  - [Infinite]: Define colists and map to Haskell lists?

-- Missing from the Haskell Prelude:
--
--     Enum(succ, pred, toEnum, fromEnum, enumFrom, enumFromThen,
--          enumFromTo, enumFromThenTo),      [Int, Partial]
--     Bounded(minBound, maxBound),
--
--     Int, Integer, Float        [Int, Float]
--     Rational, Word,            [Int]
--
--     Num((+), (-), (*), negate, abs, signum, fromInteger),
--     Real(toRational),
--     Integral(quot, rem, div, mod, quotRem, divMod, toInteger),
--     Fractional((/), recip, fromRational),
--     Floating(pi, exp, log, sqrt, (**), logBase, sin, cos, tan,
--              asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh),
--     RealFrac(properFraction, truncate, round, ceiling, floor),
--     RealFloat(floatRadix, floatDigits, floatRange, decodeFloat,
--               encodeFloat, exponent, significand, scaleFloat, isNaN,
--               isInfinite, isDenormalized, isIEEE, isNegativeZero, atan2),
--
--     subtract, even, odd, gcd, lcm, (^), (^^),
--     fromIntegral, realToFrac,
--
--     foldr1, foldl1, maximum, minimum      [Partial]
--     length                                [Int]
--     product, sum
--
--     until, error, errorWithoutStackTrace, undefined    [Partial]
--
--     head, last, tail, init, (!!)    [Partial]
--     iterate, repeat, cycle          [Infinite]
--     take, drop, splitAt             [Int]
--
--     ShowS, Show(showsPrec, showList, show),
--     shows, showChar, showString, showParen,
--
--     ReadS, Read(readsPrec, readList),
--     reads, readParen, read, lex,
--
--     IO, putChar, putStr, putStrLn, print,
--     getChar, getLine, getContents, interact,
--     FilePath, readFile, writeFile, appendFile, readIO, readLn,
--     IOError, ioError, userError,

--------------------------------------------------
-- Type variables

variable
  a b c d e : Set
  f m s t   : Set → Set


--------------------------------------------------
-- Functions

id : a → a
id x = x

infixr 9 _∘_
_∘_ : (b → c) → (a → b) → a → c
(f ∘ g) x = f (g x)

flip : (a → b → c) → b → a → c
flip f x y = f y x

const : a → b → a
const x _ = x

infixr 0 _$_ _$!_
_$_ : (a → b) → a → b
f $ x = f x

_$!_ : (a → b) → a → b
f $! x = primForce x f

seq : a → b → b
seq x y = const y $! x

infix -1 case_of_
case_of_ : a → (a → b) → b
case x of f = f x

asTypeOf : a → a → a
asTypeOf x _ = x

--------------------------------------------------
-- Tuples

infixr 5 _∷_
data Tuple : List Set → Set where
  []  : Tuple []
  _∷_ : ∀ {as} → a → Tuple as → Tuple (a ∷ as)

infix 3 _×_ _×_×_

_×_ : (a b : Set) → Set
a × b = Tuple (a ∷ b ∷ [])

_×_×_ : (a b c : Set) → Set
a × b × c = Tuple (a ∷ b ∷ c ∷ [])

infix -1 _,_ _,_,_

pattern _,_     x y     = x Tuple.∷ y Tuple.∷ []
pattern _,_,_   x y z   = x Tuple.∷ y Tuple.∷ z Tuple.∷ []

uncurry : (a → b → c) → a × b → c
uncurry f (x , y) = f x y

curry : (a × b → c) → a → b → c
curry f x y = f (x , y)

fst : a × b → a
fst (x , _) = x

snd : a × b → b
snd (_ , y) = y

private
  first : (a → b) → a × c → b × c
  first f (x , y) = f x , y

  second : (a → b) → c × a → c × b
  second f (x , y) = x , f y

  _***_ : (a → b) → (c → d) → a × c → b × d
  (f *** g) (x , y) = f x , g y


--------------------------------------------------
-- Booleans

infixr 3 _&&_
_&&_ : Bool → Bool → Bool
false && _ = false
true  && x = x

infixr 2 _||_
_||_ : Bool → Bool → Bool
false || x = x
true  || _ = true

not : Bool → Bool
not false = true
not true  = false

otherwise : Bool
otherwise = true


--------------------------------------------------
-- List

map : (a → b) → List a → List b
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

infixr 5 _++_
_++_ : ∀ {ℓ} {a : Set ℓ} → List a → List a → List a
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

filter : (a → Bool) → List a → List a
filter p []       = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

scanl : (b → a → b) → b → List a → List b
scanl f z []       = z ∷ []
scanl f z (x ∷ xs) = z ∷ scanl f (f z x) xs

scanr : (a → b → b) → b → List a → List b
scanr f z [] = z ∷ []
scanr f z (x ∷ xs) =
  case scanr f z xs of λ where
    []         → [] -- impossible
    qs@(q ∷ _) → f x q ∷ qs

scanl1 : (a → a → a) → List a → List a
scanl1 f []       = []
scanl1 f (x ∷ xs) = scanl f x xs

scanr1 : (a → a → a) → List a → List a
scanr1 f []       = []
scanr1 f (x ∷ []) = x ∷ []
scanr1 f (x ∷ xs) =
  case scanr1 f xs of λ where
    []         → [] -- impossible
    qs@(q ∷ _) → f x q ∷ qs

takeWhile : (a → Bool) → List a → List a
takeWhile p [] = []
takeWhile p (x ∷ xs) = if p x then x ∷ takeWhile p xs else []

dropWhile : (a → Bool) → List a → List a
dropWhile p [] = []
dropWhile p (x ∷ xs) = if p x then dropWhile p xs else x ∷ xs

span : (a → Bool) → List a → List a × List a
span p [] = [] , []
span p (x ∷ xs) = if p x then first (x ∷_) (span p xs)
                         else ([] , x ∷ xs)

break : (a → Bool) → List a → List a × List a
break p = span (not ∘ p)

zipWith : (a → b → c) → List a → List b → List c
zipWith f []       _        = []
zipWith f _        []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

zip : List a → List b → List (a × b)
zip = zipWith _,_

zipWith3 : (a → b → c → d) → List a → List b → List c → List d
zipWith3 f []       _        _        = []
zipWith3 f _        []       _        = []
zipWith3 f _        _        []       = []
zipWith3 f (x ∷ xs) (y ∷ ys) (z ∷ zs) = f x y z ∷ zipWith3 f xs ys zs

zip3 : List a → List b → List c → List (a × b × c)
zip3 = zipWith3 _,_,_

unzip : List (a × b) → List a × List b
unzip []              = [] , []
unzip ((x , y) ∷ xys) = (x ∷_) *** (y ∷_) $ unzip xys

unzip3 : List (a × b × c) → List a × List b × List c
unzip3 []                   = [] , [] , []
unzip3 ((x , y , z) ∷ xyzs) =
  case unzip3 xyzs of λ where
    (xs , ys , zs) → x ∷ xs , y ∷ ys , z ∷ zs


--------------------------------------------------
-- Maybe

data Maybe (a : Set) : Set where
  Nothing : Maybe a
  Just    : a -> Maybe a

maybe : b → (a → b) → Maybe a → b
maybe n j Nothing  = n
maybe n j (Just x) = j x


--------------------------------------------------
-- Either

data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b

either : (a → c) → (b → c) → Either a b → c
either f g (Left  x) = f x
either f g (Right y) = g y


--------------------------------------------------
-- Ordering

data Ordering : Set where
  LT EQ GT : Ordering

--------------------------------------------------
-- String

String = List Char

instance
  iIsStringString : IsString String
  iIsStringString .IsString.Constraint _ = ⊤
  iIsStringString .fromString s = Str.primStringToList s

--------------------------------------------------
-- Semigroup

record Semigroup (a : Set) : Set where
  infixr 6 _<>_
  field
    _<>_ : a → a → a

open Semigroup ⦃ ... ⦄ public

instance
  iSemigroupList : Semigroup (List a)
  iSemigroupList ._<>_ = _++_

  iSemigroupMaybe : ⦃ Semigroup a ⦄ → Semigroup (Maybe a)
  iSemigroupMaybe ._<>_          Nothing m = m
  iSemigroupMaybe ._<>_ m        Nothing   = m
  iSemigroupMaybe ._<>_ (Just x) (Just y)  = Just (x <> y)

  iSemigroupEither : Semigroup (Either a b)
  iSemigroupEither ._<>_ (Left _) e = e
  iSemigroupEither ._<>_ e        _ = e

  iSemigroupFun : ⦃ Semigroup b ⦄ → Semigroup (a → b)
  iSemigroupFun ._<>_ f g x = f x <> g x

  iSemigroupUnit : Semigroup ⊤
  iSemigroupUnit ._<>_ _ _ = tt

  iSemigroupTuple₀ : Semigroup (Tuple [])
  iSemigroupTuple₀ ._<>_ _ _ = []

  iSemigroupTuple : ∀ {as} → ⦃ Semigroup a ⦄ → ⦃ Semigroup (Tuple as) ⦄ → Semigroup (Tuple (a ∷ as))
  iSemigroupTuple ._<>_ (x ∷ xs) (y ∷ ys) = x <> y ∷ xs <> ys

  iSemigroupOrdering : Semigroup Ordering
  iSemigroupOrdering ._<>_ LT _ = LT
  iSemigroupOrdering ._<>_ EQ o = o
  iSemigroupOrdering ._<>_ GT _ = GT


--------------------------------------------------
-- Monoid

record Monoid (a : Set) : Set where
  field
    mempty : a
    overlap ⦃ super ⦄ : Semigroup a

  mappend : a → a → a
  mappend = _<>_

  mconcat : List a → a
  mconcat []       = mempty
  mconcat (x ∷ xs) = x <> mconcat xs

open Monoid ⦃ ... ⦄ public

instance
  iMonoidList : Monoid (List a)
  iMonoidList .mempty = []

  iMonoidMaybe : ⦃ Semigroup a ⦄ → Monoid (Maybe a)
  iMonoidMaybe .mempty = Nothing

  iMonoidFun : ⦃ Monoid b ⦄ → Monoid (a → b)
  iMonoidFun .mempty _ = mempty

  iMonoidUnit : Monoid ⊤
  iMonoidUnit .mempty = tt

  iMonoidTuple₀ : Monoid (Tuple [])
  iMonoidTuple₀ .mempty = []

  iMonoidTuple : ∀ {as} → ⦃ Monoid a ⦄ → ⦃ Monoid (Tuple as) ⦄ → Monoid (Tuple (a ∷ as))
  iMonoidTuple .mempty = mempty ∷ mempty

  iMonoidOrdering : Monoid Ordering
  iMonoidOrdering .mempty = EQ

private
  MonoidEndo : Monoid (a → a)
  MonoidEndo .mempty      = id
  MonoidEndo .super ._<>_ = _∘_

  MonoidEndoᵒᵖ : Monoid (a → a)
  MonoidEndoᵒᵖ .mempty      = id
  MonoidEndoᵒᵖ .super ._<>_ = flip _∘_

  MonoidConj : Monoid Bool
  MonoidConj .mempty      = true
  MonoidConj .super ._<>_ = _&&_

  MonoidDisj : Monoid Bool
  MonoidDisj .mempty      = false
  MonoidDisj .super ._<>_ = _||_


--------------------------------------------------
-- Eq --

record Eq (a : Set) : Set where
  infix 4 _==_ _/=_
  field
    _==_ : a → a → Bool

  _/=_ : a → a → Bool
  x /= y = not (x == y)

open Eq ⦃ ... ⦄ public

instance
  iEqNat : Eq Nat
  iEqNat ._==_ = Nat._==_

  iEqInteger : Eq Integer
  iEqInteger ._==_ = eqInteger

  iEqInt : Eq Int
  iEqInt ._==_ = eqInt

  iEqWord : Eq Word64
  iEqWord ._==_ = eqWord

  iEqBool : Eq Bool
  iEqBool ._==_ false false = true
  iEqBool ._==_ true  true  = true
  iEqBool ._==_ _     _     = false

  iEqChar : Eq Char
  iEqChar ._==_ = primCharEquality

  iEqUnit : Eq ⊤
  iEqUnit ._==_ _ _ = true

  iEqTuple₀ : Eq (Tuple [])
  iEqTuple₀ ._==_ _ _ = true

  iEqTuple : ∀ {as} → ⦃ Eq a ⦄ → ⦃ Eq (Tuple as) ⦄ → Eq (Tuple (a ∷ as))
  iEqTuple ._==_ (x ∷ xs) (y ∷ ys) = x == y && xs == ys

  iEqList : ⦃ Eq a ⦄ → Eq (List a)
  iEqList ._==_ []       []       = false
  iEqList ._==_ (x ∷ xs) (y ∷ ys) = x == y && xs == ys
  iEqList ._==_ _        _        = false

  iEqMaybe : ⦃ Eq a ⦄ → Eq (Maybe a)
  iEqMaybe ._==_ Nothing  Nothing  = true
  iEqMaybe ._==_ (Just x) (Just y) = x == y
  iEqMaybe ._==_ _        _        = false

  iEqEither : ⦃ Eq a ⦄ → ⦃ Eq b ⦄ → Eq (Either a b)
  iEqEither ._==_ (Left  x) (Left  y) = x == y
  iEqEither ._==_ (Right x) (Right y) = x == y
  iEqEither ._==_ _        _          = false

  iEqOrdering : Eq Ordering
  iEqOrdering ._==_ LT LT = true
  iEqOrdering ._==_ EQ EQ = true
  iEqOrdering ._==_ GT GT = true
  iEqOrdering ._==_ _  _  = false

--------------------------------------------------
-- Ord --

record Ord (a : Set) : Set where
  field
    compare : a → a → Ordering
    overlap ⦃ super ⦄ : Eq a

  infix 4 _<_ _>_ _<=_ _>=_

  _<_ : a → a → Bool
  x < y = compare x y == LT

  _<=_ : a → a → Bool
  x <= y = compare x y /= GT

  _>_ : a → a → Bool
  x > y = compare x y == GT

  _>=_ : a → a → Bool
  x >= y = compare x y /= LT

  max : a → a → a
  max x y = if x >= y then x else y

  min : a → a → a
  min x y = if x <= y then x else y

open Ord ⦃ ... ⦄ public

private
  compareFromLt : ⦃ Eq a ⦄ → (a → a → Bool) → a → a → Ordering
  compareFromLt _<_ x y = if x < y then LT else if x == y then EQ else GT

instance
  iOrdNat : Ord Nat
  iOrdNat .compare = compareFromLt Nat._<_

  iOrdInteger : Ord Integer
  iOrdInteger .compare = compareFromLt ltInteger

  iOrdInt : Ord Int
  iOrdInt .compare = compareFromLt ltInt

  iOrdWord : Ord Word64
  iOrdWord .compare = compareFromLt ltWord

  iOrdBool : Ord Bool
  iOrdBool .compare false true  = LT
  iOrdBool .compare true  false = GT
  iOrdBool .compare _     _     = EQ

  iOrdTuple₀ : Ord (Tuple [])
  iOrdTuple₀ .compare _ _ = EQ

  iOrdTuple : ∀ {as} → ⦃ Ord a ⦄ → ⦃ Ord (Tuple as) ⦄ → Ord (Tuple (a ∷ as))
  iOrdTuple .compare (x ∷ xs) (y ∷ ys) = compare x y <> compare xs ys

  iOrdList : ⦃ Ord a ⦄ → Ord (List a)
  iOrdList .compare []       []       = EQ
  iOrdList .compare []       (_ ∷ _)  = LT
  iOrdList .compare (_ ∷ _)  []       = GT
  iOrdList .compare (x ∷ xs) (y ∷ ys) = compare x y <> compare xs ys

  iOrdMaybe : ⦃ Ord a ⦄ → Ord (Maybe a)
  iOrdMaybe .compare Nothing  Nothing  = EQ
  iOrdMaybe .compare Nothing  (Just _) = LT
  iOrdMaybe .compare (Just _) Nothing  = GT
  iOrdMaybe .compare (Just x) (Just y) = compare x y

  iOrdEither : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → Ord (Either a b)
  iOrdEither .compare (Left  x) (Left  y) = compare x y
  iOrdEither .compare (Left  _) (Right _) = LT
  iOrdEither .compare (Right _) (Left  _) = GT
  iOrdEither .compare (Right x) (Right y) = compare x y

  iOrdOrdering : Ord Ordering
  iOrdOrdering .compare LT LT = EQ
  iOrdOrdering .compare LT _  = LT
  iOrdOrdering .compare _  LT = GT
  iOrdOrdering .compare EQ EQ = EQ
  iOrdOrdering .compare EQ GT = LT
  iOrdOrdering .compare GT EQ = GT
  iOrdOrdering .compare GT GT = EQ


--------------------------------------------------
-- Foldable

record Foldable (t : Set → Set) : Set₁ where
  field
    foldMap : ⦃ Monoid b ⦄ → (a → b) → t a → b

  foldr : (a → b → b) → b → t a → b
  foldr f z t = foldMap ⦃ MonoidEndo ⦄ f t z

  foldl : (b → a → b) → b → t a → b
  foldl f z t = foldMap ⦃ MonoidEndoᵒᵖ ⦄ (flip f) t z

  any : (a → Bool) → t a → Bool
  any = foldMap ⦃ MonoidDisj ⦄

  all : (a → Bool) → t a → Bool
  all = foldMap ⦃ MonoidConj ⦄

  and : t Bool → Bool
  and = all id

  or : t Bool → Bool
  or = any id

  null : t a → Bool
  null = all (const false)

  concat : t (List a) → List a
  concat = foldMap id

  concatMap : (a → List b) → t a → List b
  concatMap = foldMap

  elem : ⦃ Eq a ⦄ → a → t a → Bool
  elem x = foldMap ⦃ MonoidDisj ⦄ (x ==_)

  notElem : ⦃ Eq a ⦄ → a → t a → Bool
  notElem x t = not (elem x t)

  toList : t a → List a
  toList = foldr _∷_ []


open Foldable ⦃ ... ⦄ public

instance
  iFoldableList : Foldable List
  iFoldableList .foldMap f []       = mempty
  iFoldableList .foldMap f (x ∷ xs) = f x <> foldMap f xs

  iFoldableMaybe : Foldable Maybe
  iFoldableMaybe .foldMap _ Nothing  = mempty
  iFoldableMaybe .foldMap f (Just x) = f x

  iFoldableEither : Foldable (Either a)
  iFoldableEither .foldMap _ (Left _) = mempty
  iFoldableEither .foldMap f (Right x) = f x

  iFoldablePair : Foldable (a ×_)
  iFoldablePair .foldMap f (_ , x) = f x


--------------------------------------------------
-- String functions

private
  cons : Char → List String → List String
  cons c []       = (c ∷ []) ∷ []
  cons c (s ∷ ss) = (c ∷ s) ∷ ss

lines : String → List String
lines []         = []
lines ('\n' ∷ s) = [] ∷ lines s
lines (c    ∷ s) = cons c (lines s)

private
 mutual
  space : String → List String
  space [] = []
  space (c ∷ s) = if primIsSpace c then space s else cons c (word s)

  word  : String → List String
  word []      = []
  word (c ∷ s) = if primIsSpace c then [] ∷ space s else cons c (word s)

words : String → List String
words [] = []
words s@(c ∷ s₁) = if primIsSpace c then space s₁ else word s

unlines : List String → String
unlines = concatMap (_++ "\n")

unwords : List String → String
unwords [] = ""
unwords (w ∷ []) = w
unwords (w ∷ ws) = w ++ ' ' ∷ unwords ws


-------------------------------------------------
-- More List functions

reverse : List a → List a
reverse = foldl (flip _∷_) []

lookup : ⦃ Eq a ⦄ → a → List (a × b) → Maybe b
lookup x []              = Nothing
lookup x ((x₁ , y) ∷ xs) = if x == x₁ then Just y else lookup x xs


--------------------------------------------------
-- Functor

record Functor (f : Set → Set) : Set₁ where
  field
    fmap : (a → b) → f a → f b

  infixl 1 _<&>_
  infixl 4 _<$>_ _<$_ _$>_

  _<$>_ : (a → b) → f a → f b
  _<$>_ = fmap

  _<&>_ : f a → (a → b) → f b
  m <&> f = fmap f m

  _<$_ : a → f b → f a
  x <$ m = fmap (const x) m

  _$>_ : f a → b → f b
  m $> x = x <$ m

  void : f a → f ⊤
  void = tt <$_

open Functor ⦃ ... ⦄ public

instance
  iFunctorList : Functor List
  iFunctorList .fmap = map

  iFunctorMaybe : Functor Maybe
  iFunctorMaybe .fmap f Nothing  = Nothing
  iFunctorMaybe .fmap f (Just x) = Just (f x)

  iFunctorEither : Functor (Either a)
  iFunctorEither .fmap f (Left  x) = Left x
  iFunctorEither .fmap f (Right y) = Right (f y)

  iFunctorFun : Functor (λ b → a → b)
  iFunctorFun .fmap = _∘_

  iFunctorTuple₂ : Functor (a ×_)
  iFunctorTuple₂ .fmap f (x , y) = x , f y

  iFunctorTuple₃ : Functor (a × b ×_)
  iFunctorTuple₃ .fmap f (x , y , z) = x , y , f z

  iFunctorTuple₄ : Functor (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))
  iFunctorTuple₄ .fmap f (x ∷ y ∷ z ∷ w ∷ []) = x ∷ y ∷ z ∷ f w ∷ []


--------------------------------------------------
-- Applicative

record Applicative (f : Set → Set) : Set₁ where
  infixl 4 _<*>_
  field
    pure  : a → f a
    _<*>_ : f (a → b) → f a → f b
    overlap ⦃ super ⦄ : Functor f

  _<*_ : f a → f b → f a
  x <* y = const <$> x <*> y

  _*>_ : f a → f b → f b
  x *> y = const id <$> x <*> y

open Applicative ⦃ ... ⦄ public

instance
  iApplicativeList : Applicative List
  iApplicativeList .pure x      = x ∷ []
  iApplicativeList ._<*>_ fs xs = concatMap (λ f → map f xs) fs

  iApplicativeMaybe : Applicative Maybe
  iApplicativeMaybe .pure = Just
  iApplicativeMaybe ._<*>_ (Just f) (Just x) = Just (f x)
  iApplicativeMaybe ._<*>_ _        _        = Nothing

  iApplicativeEither : Applicative (Either a)
  iApplicativeEither .pure = Right
  iApplicativeEither ._<*>_ (Right f) (Right x) = Right (f x)
  iApplicativeEither ._<*>_ (Left e)  _         = Left e
  iApplicativeEither ._<*>_ _         (Left e)  = Left e

  iApplicativeFun : Applicative (λ b → a → b)
  iApplicativeFun .pure        = const
  iApplicativeFun ._<*>_ f g x = f x (g x)

  iApplicativeTuple₂ : ⦃ Monoid a ⦄ → Applicative (a ×_)
  iApplicativeTuple₂ .pure x                = mempty , x
  iApplicativeTuple₂ ._<*>_ (a , f) (b , x) = a <> b , f x

  iApplicativeTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Applicative (a × b ×_)
  iApplicativeTuple₃ .pure x                          = mempty , mempty , x
  iApplicativeTuple₃ ._<*>_ (a , b , f) (a₁ , b₁ , x) = a <> a₁ , b <> b₁ , f x

  iApplicativeTuple₄ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ⦃ Monoid c ⦄ →
                       Applicative (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))
  iApplicativeTuple₄ .pure x                          = mempty ∷ mempty ∷ mempty ∷ x ∷ []
  iApplicativeTuple₄ ._<*>_ (a ∷ b ∷ c ∷ f ∷ []) (a₁ ∷ b₁ ∷ c₁ ∷ x ∷ []) =
    a <> a₁ ∷ b <> b₁ ∷ c <> c₁ ∷ f x ∷ []


--------------------------------------------------
-- Monad

record Monad (m : Set → Set) : Set₁ where
  field
    _>>=_ : m a → (a → m b) → m b
    overlap ⦃ super ⦄ : Applicative m

  return : a → m a
  return = pure

  _>>_ : m a → m b → m b
  m >> m₁ = m >>= λ _ → m₁

  _=<<_ : (a → m b) → m a → m b
  _=<<_ = flip _>>=_

open Monad ⦃ ... ⦄ public

mapM₋ : ⦃ Monad m ⦄ → ⦃ Foldable t ⦄ → (a → m b) → t a → m ⊤
mapM₋ f = foldr (λ x k → f x >> k) (pure tt)

sequence₋ : ⦃ Monad m ⦄ → ⦃ Foldable t ⦄ → t (m a) → m ⊤
sequence₋ = foldr _>>_ (pure tt)

instance
  iMonadList : Monad List
  iMonadList ._>>=_ = flip concatMap

  iMonadMaybe : Monad Maybe
  iMonadMaybe ._>>=_ m k = maybe Nothing k m

  iMonadEither : Monad (Either a)
  iMonadEither ._>>=_ m k = either Left k m

  iMonadFun : Monad (λ b → a → b)
  iMonadFun ._>>=_ f k r = k (f r) r

  iMonadTuple₂ : ⦃ Monoid a ⦄ → Monad (a ×_)
  iMonadTuple₂ ._>>=_ (a , x) k = first (a <>_) (k x)

  iMonadTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Monad (a × b ×_)
  iMonadTuple₃ ._>>=_ (a , b , x) k =
    case k x of λ where
      (a₁ , b₁ , y) → a <> a₁ , b <> b₁ , y

  iMonadTuple₄ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ⦃ Monoid c ⦄ →
                 Monad (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))
  iMonadTuple₄ ._>>=_ (a ∷ b ∷ c ∷ x ∷ []) k =
    case k x of λ where
      (a₁ ∷ b₁ ∷ c₁ ∷ y ∷ []) → a <> a₁ ∷ b <> b₁ ∷ c <> c₁ ∷ y ∷ []

record MonadFail (m : Set → Set) : Set₁ where
  field
    fail : String → m a
    overlap ⦃ super ⦄ : Monad m

open MonadFail ⦃ ... ⦄ public

instance
  MonadFailList : MonadFail List
  MonadFailList .fail _ = []

  MonadFailMaybe : MonadFail Maybe
  MonadFailMaybe .fail _ = Nothing


--------------------------------------------------
-- Traversable

record Traversable (t : Set → Set) : Set₁ where
  field
    traverse : ⦃ Applicative f ⦄ → (a → f b) → t a → f (t b)
    overlap ⦃ functor ⦄ : Functor t
    overlap ⦃ foldable ⦄ : Foldable t

  sequenceA : ⦃ Applicative f ⦄ → t (f a) → f (t a)
  sequenceA = traverse id

  mapM : ⦃ Monad m ⦄ → (a → m b) → t a → m (t b)
  mapM = traverse

  sequence : ⦃ Monad m ⦄ → t (m a) → m (t a)
  sequence = sequenceA

open Traversable ⦃ ... ⦄ public

instance
  iTraversableList : Traversable List
  iTraversableList .traverse f []       = pure []
  iTraversableList .traverse f (x ∷ xs) = ⦇ f x ∷ traverse f xs ⦈

  iTraversableMaybe : Traversable Maybe
  iTraversableMaybe .traverse f Nothing  = pure Nothing
  iTraversableMaybe .traverse f (Just x) = Just <$> f x

  iTraversableEither : Traversable (Either a)
  iTraversableEither .traverse f (Left  x) = pure (Left x)
  iTraversableEither .traverse f (Right y) = Right <$> f y

  iTraversablePair : Traversable (a ×_)
  iTraversablePair .traverse f (x , y) = (x ,_) <$> f y
