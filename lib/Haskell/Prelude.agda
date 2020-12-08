{-# OPTIONS --no-auto-inline #-}
module Haskell.Prelude where

open import Agda.Builtin.Unit         public
open import Agda.Builtin.Nat as Nat   public hiding (_==_; _<_; _+_; _*_; _-_)
open import Agda.Builtin.List         public
open import Agda.Builtin.Bool         public
open import Agda.Builtin.Float        public renaming (Float to Double)
open import Agda.Builtin.Char         public
open import Agda.Builtin.FromString   public
import Agda.Builtin.String as Str
open import Agda.Builtin.Strict
open import Agda.Builtin.FromNat      public using (Number; fromNat)
open import Agda.Builtin.FromNeg      public using (Negative; fromNeg)
open import Agda.Builtin.Word         public renaming (Word64 to Word)
open import Agda.Builtin.Equality     public
open import Agda.Builtin.Int using (pos; negsuc)

open import Haskell.Prim
open Haskell.Prim public using (TypeError; ⊥; if_then_else_; iNumberNat; IsTrue; IsFalse; All; allNil; allCons; NonEmpty)

open import Haskell.Prim.Integer
open Haskell.Prim.Integer public using (Integer; iNumberInteger; iNegativeInteger; isNegativeInteger; IsNonNegativeInteger)

open import Haskell.Prim.Int renaming (Int64 to Int)
open Haskell.Prim.Int public using (iNumberInt; iNegativeInt; isNegativeInt; IsNonNegativeInt) renaming (Int64 to Int)

open import Haskell.Prim.Double
open Haskell.Prim.Double public using (iNumberDouble; iNegativeDouble)

open import Haskell.Prim.Word

-- Problematic features
--  - [Partial]:  Could pass implicit/instance arguments to prove totality.
--  - [Float]:    Or Float (Agda floats are Doubles)
--  - [Infinite]: Define colists and map to Haskell lists?

-- Missing from the Haskell Prelude:
--
--     Enum(succ, pred, toEnum, fromEnum, enumFrom, enumFromThen,
--          enumFromTo, enumFromThenTo),      [Partial]
--     Bounded(minBound, maxBound),
--
--     Float        [Float]
--     Rational
--
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
--
--     until, error, errorWithoutStackTrace, undefined    [Partial]
--
--     iterate, repeat, cycle          [Infinite]
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
-- Eq

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

  iEqDouble : Eq Double
  iEqDouble ._==_ = primFloatNumericalEquality

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
-- Ord

record Ord (a : Set) : Set where
  field
    compare : a → a → Ordering
    _<_  : a → a → Bool
    _>_  : a → a → Bool
    _>=_ : a → a → Bool
    _<=_ : a → a → Bool
    max  : a → a → a
    min  : a → a → a
    overlap ⦃ super ⦄ : Eq a

  infix 4 _<_ _>_ _<=_ _>=_

open Ord ⦃ ... ⦄ public

ordFromCompare : ⦃ Eq a ⦄ → (a → a → Ordering) → Ord a
ordFromCompare cmp .compare = cmp
ordFromCompare cmp ._<_  x y = cmp x y == LT
ordFromCompare cmp ._>_  x y = cmp x y == GT
ordFromCompare cmp ._<=_ x y = cmp x y /= GT
ordFromCompare cmp ._>=_ x y = cmp x y /= LT
ordFromCompare cmp .max  x y = if cmp x y == LT then y else x
ordFromCompare cmp .min  x y = if cmp x y == GT then y else x

ordFromLessThan : ⦃ Eq a ⦄ → (a → a → Bool) → Ord a
ordFromLessThan _<_ .compare x y = if x < y then LT else if x == y then EQ else GT
ordFromLessThan _<_ ._<_  x y = x < y
ordFromLessThan _<_ ._>_  x y = y < x
ordFromLessThan _<_ ._<=_ x y = x < y || x == y
ordFromLessThan _<_ ._>=_ x y = y < x || x == y
ordFromLessThan _<_ .max  x y = if x < y then y else x
ordFromLessThan _<_ .min  x y = if y < x then y else x

ordFromLessEq : ⦃ Eq a ⦄ → (a → a → Bool) → Ord a
ordFromLessEq _<=_ .compare x y = if x == y then EQ else if x <= y then LT else GT
ordFromLessEq _<=_ ._<_  x y = x <= y && not (x == y)
ordFromLessEq _<=_ ._>_  x y = y <= x && not (x == y)
ordFromLessEq _<=_ ._<=_ x y = x <= y
ordFromLessEq _<=_ ._>=_ x y = y <= x
ordFromLessEq _<=_ .max  x y = if y <= x then x else y
ordFromLessEq _<=_ .min  x y = if x <= y then x else y

private
  compareFromLt : ⦃ Eq a ⦄ → (a → a → Bool) → a → a → Ordering
  compareFromLt _<_ x y = if x < y then LT else if x == y then EQ else GT

instance
  iOrdNat : Ord Nat
  iOrdNat = ordFromLessThan Nat._<_

  iOrdInteger : Ord Integer
  iOrdInteger = ordFromLessThan ltInteger

  iOrdInt : Ord Int
  iOrdInt = ordFromLessThan ltInt

  iOrdWord : Ord Word64
  iOrdWord = ordFromLessThan ltWord

  iOrdDouble : Ord Double
  iOrdDouble = ordFromLessThan primFloatNumericalLess

  iOrdBool : Ord Bool
  iOrdBool = ordFromCompare λ where
    false true  → LT
    true  false → GT
    _     _     → EQ

  iOrdTuple₀ : Ord (Tuple [])
  iOrdTuple₀ = ordFromCompare λ _ _ → EQ

  iOrdTuple : ∀ {as} → ⦃ Ord a ⦄ → ⦃ Ord (Tuple as) ⦄ → Ord (Tuple (a ∷ as))
  iOrdTuple = ordFromCompare λ where (x ∷ xs) (y ∷ ys) → compare x y <> compare xs ys

compareList : ⦃ Ord a ⦄ → List a → List a → Ordering
compareList []       []       = EQ
compareList []       (_ ∷ _)  = LT
compareList (_ ∷ _)  []       = GT
compareList (x ∷ xs) (y ∷ ys) = compare x y <> compareList xs ys

instance
  iOrdList : ⦃ Ord a ⦄ → Ord (List a)
  iOrdList = ordFromCompare compareList

  iOrdMaybe : ⦃ Ord a ⦄ → Ord (Maybe a)
  iOrdMaybe = ordFromCompare λ where
    Nothing  Nothing  → EQ
    Nothing  (Just _) → LT
    (Just _) Nothing  → GT
    (Just x) (Just y) → compare x y

  iOrdEither : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → Ord (Either a b)
  iOrdEither = ordFromCompare λ where
    (Left  x) (Left  y) → compare x y
    (Left  _) (Right _) → LT
    (Right _) (Left  _) → GT
    (Right x) (Right y) → compare x y

  iOrdOrdering : Ord Ordering
  iOrdOrdering = ordFromCompare λ where
    LT LT → EQ
    LT _  → LT
    _  LT → GT
    EQ EQ → EQ
    EQ GT → LT
    GT EQ → GT
    GT GT → EQ


--------------------------------------------------
-- Num

record Num (a : Set) : Set₁ where
  infixl 6 _+_ _-_
  infixl 7 _*_
  field
    MinusOK       : a → a → Set
    NegateOK      : a → Set
    FromIntegerOK : Integer → Set
    _+_           : a → a → a
    _-_           : (x y : a) → ⦃ MinusOK x y ⦄ → a
    _*_           : a → a → a
    negate        : (x : a) → ⦃ NegateOK x ⦄ → a
    abs           : a → a
    signum        : a → a
    fromInteger   : (n : Integer) → ⦃ FromIntegerOK n ⦄ → a
    overlap ⦃ number ⦄  : Number a
    overlap ⦃ numZero ⦄ : number .Number.Constraint 0
    overlap ⦃ numOne ⦄  : number .Number.Constraint 1

open Num ⦃ ... ⦄ public hiding (FromIntegerOK; number)

instance
  iNumNat : Num Nat
  iNumNat .MinusOK n m      = IsFalse (n Nat.< m)
  iNumNat .NegateOK 0       = ⊤
  iNumNat .NegateOK (suc _) = ⊥
  iNumNat .Num.FromIntegerOK (negsuc _) = ⊥
  iNumNat .Num.FromIntegerOK (pos _) = ⊤
  iNumNat ._+_ n m = n Nat.+ m
  iNumNat ._-_ n m = n Nat.- m
  iNumNat ._*_ n m = n Nat.* m
  iNumNat .negate n = n
  iNumNat .abs    n = n
  iNumNat .signum 0       = 0
  iNumNat .signum (suc n) = 1
  iNumNat .fromInteger (pos n) = n
  iNumNat .fromInteger (negsuc _) ⦃ () ⦄

  iNumInt : Num Int
  iNumInt .MinusOK _ _         = ⊤
  iNumInt .NegateOK _          = ⊤
  iNumInt .Num.FromIntegerOK _ = ⊤
  iNumInt ._+_ x y             = addInt x y
  iNumInt ._-_ x y             = subInt x y
  iNumInt ._*_ x y             = mulInt x y
  iNumInt .negate x            = negateInt x
  iNumInt .abs x               = absInt x
  iNumInt .signum x            = signInt x
  iNumInt .fromInteger n       = integerToInt n

  iNumInteger : Num Integer
  iNumInteger .MinusOK _ _ = ⊤
  iNumInteger .NegateOK _          = ⊤
  iNumInteger .Num.FromIntegerOK _ = ⊤
  iNumInteger ._+_ x y             = addInteger x y
  iNumInteger ._-_ x y             = subInteger x y
  iNumInteger ._*_ x y             = mulInteger x y
  iNumInteger .negate x            = negateInteger x
  iNumInteger .abs x               = absInteger x
  iNumInteger .signum x            = signInteger x
  iNumInteger .fromInteger n       = n

  iNumWord : Num Word
  iNumWord .MinusOK _ _         = ⊤
  iNumWord .NegateOK _          = ⊤
  iNumWord .Num.FromIntegerOK _ = ⊤
  iNumWord ._+_ x y             = addWord x y
  iNumWord ._-_ x y             = subWord x y
  iNumWord ._*_ x y             = mulWord x y
  iNumWord .negate x            = negateWord x
  iNumWord .abs x               = x
  iNumWord .signum x            = if x == 0 then 0 else 1
  iNumWord .fromInteger n       = integerToWord n

  iNumDouble : Num Double
  iNumDouble .MinusOK _ _         = ⊤
  iNumDouble .NegateOK _          = ⊤
  iNumDouble .Num.FromIntegerOK _ = ⊤
  iNumDouble ._+_ x y             = primFloatPlus x y
  iNumDouble ._-_ x y             = primFloatMinus x y
  iNumDouble ._*_ x y             = primFloatTimes x y
  iNumDouble .negate x            = primFloatMinus 0.0 x
  iNumDouble .abs x               = if x < 0.0 then primFloatMinus 0.0 x else x
  iNumDouble .signum x            = case compare x 0.0 of λ where
                                      LT → -1.0
                                      EQ → x
                                      GT → 1.0
  iNumDouble .fromInteger (pos    n) = fromNat n
  iNumDouble .fromInteger (negsuc n) = fromNeg (suc n)

private
  MonoidSum : ⦃ iNum : Num a ⦄ → Monoid a
  MonoidSum .mempty      = 0
  MonoidSum .super ._<>_ = _+_

  MonoidProduct : ⦃ iNum : Num a ⦄ → Monoid a
  MonoidProduct .mempty      = 1
  MonoidProduct .super ._<>_ = _*_


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

  sum : ⦃ iNum : Num a ⦄ → t a → a
  sum = foldMap ⦃ MonoidSum ⦄ id

  product : ⦃ iNum : Num a ⦄ → t a → a
  product = foldMap ⦃ MonoidProduct ⦄ id

  length : t a → Int
  length = foldMap ⦃ MonoidSum ⦄ (const 1)

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

lengthNat : List a → Nat
lengthNat []       = 0
lengthNat (_ ∷ xs) = 1 + lengthNat xs

infixl 9 _!!_ _!!ᴺ_

_!!ᴺ_ : (xs : List a) (n : Nat) → ⦃ IsTrue (n < lengthNat xs) ⦄ → a
(x ∷ xs) !!ᴺ zero  = x
(x ∷ xs) !!ᴺ suc n = xs !!ᴺ n

_!!_ : (xs : List a) (n : Int) ⦃ nn : IsNonNegativeInt n ⦄ → ⦃ IsTrue (intToNat n < lengthNat xs) ⦄ → a
xs !! n = xs !!ᴺ intToNat n

takeNat : Nat → List a → List a
takeNat n       [] = []
takeNat zero    xs = []
takeNat (suc n) (x ∷ xs) = x ∷ takeNat n xs

take : (n : Int) → ⦃ IsNonNegativeInt n ⦄ → List a → List a
take n xs = takeNat (intToNat n) xs

dropNat : Nat → List a → List a
dropNat n       [] = []
dropNat zero    xs = xs
dropNat (suc n) (_ ∷ xs) = dropNat n xs

drop : (n : Int) → ⦃ IsNonNegativeInt n ⦄ → List a → List a
drop n xs = dropNat (intToNat n) xs

splitAtNat : (n : Nat) → List a → List a × List a
splitAtNat _       []       = [] , []
splitAtNat 0       xs       = [] , xs
splitAtNat (suc n) (x ∷ xs) = first (x ∷_) (splitAtNat n xs)

splitAt : (n : Int) → ⦃ IsNonNegativeInt n ⦄ → List a → List a × List a
splitAt n xs = splitAtNat (intToNat n) xs

head : (xs : List a) → ⦃ NonEmpty xs ⦄ → a
head (x ∷ _) = x

tail : (xs : List a) → ⦃ NonEmpty xs ⦄ → List a
tail (_ ∷ xs) = xs

last : (xs : List a) → ⦃ NonEmpty xs ⦄ → a
last (x ∷ [])         = x
last (_ ∷ xs@(_ ∷ _)) = last xs

init : (xs : List a) → ⦃ NonEmpty xs ⦄ → List a
init (x ∷ [])         = []
init (x ∷ xs@(_ ∷ _)) = x ∷ init xs

--------------------------------------------------
-- Show

ShowS : Set
ShowS = String → String

showChar : Char → ShowS
showChar = _∷_

showString : String → ShowS
showString = _++_

showParen : Bool → ShowS → ShowS
showParen false s = s
showParen true  s = showString "(" ∘ s ∘ showString ")"

record Show (a : Set) : Set where
  field
    showsPrec : Int → a → ShowS
    showList  : List a → ShowS

  shows : a → ShowS
  shows = showsPrec 0

  show : a → String
  show x = shows x ""

defaultShowList : (a → ShowS) → List a → ShowS
defaultShowList _     []       = showString "[]"
defaultShowList shows (x ∷ xs) = showString "[" ∘ foldl (λ s x → s ∘ showString "," ∘ shows x) (shows x) xs ∘ showString "]"

open Show ⦃ ... ⦄ public

private
  makeShow : (a → String) → Show a
  makeShow sh .showsPrec _ = showString ∘ sh
  makeShow sh .showList    = defaultShowList (showString ∘ sh)

  makeShowsPrec : (Int → a → ShowS) → Show a
  makeShowsPrec shp .showsPrec = shp
  makeShowsPrec shp .showList = defaultShowList (shp 0)

instance
  iShowNat : Show Nat
  iShowNat = makeShow (Str.primStringToList ∘ Str.primShowNat)

  iShowInteger : Show Integer
  iShowInteger = makeShow showInteger

  iShowInt : Show Int
  iShowInt = makeShow showInt

  iShowWord : Show Word64
  iShowWord = makeShow showWord

  iShowDouble : Show Double
  iShowDouble = makeShow (Str.primStringToList ∘ primShowFloat)

  iShowBool : Show Bool
  iShowBool = makeShow λ where false → "False"; true → "True"

  iShowChar : Show Char
  iShowChar .showsPrec _ = showString ∘ Str.primStringToList ∘ Str.primShowChar
  iShowChar .showList    = showString ∘ Str.primStringToList ∘ Str.primShowString ∘ Str.primStringFromList

  iShowList : ⦃ Show a ⦄ → Show (List a)
  iShowList .showsPrec _ = showList
  iShowList .showList    = defaultShowList showList

private
  showApp₁ : ⦃ Show a ⦄ → Int → String → a → ShowS
  showApp₁ p tag x = showParen (p > 10) $ showString tag ∘ showString " " ∘ showsPrec 11 x

instance
  iShowMaybe : ⦃ Show a ⦄ → Show (Maybe a)
  iShowMaybe = makeShowsPrec λ where p Nothing  → showString "Nothing"
                                     p (Just x) → showApp₁ p "Just" x

  iShowEither : ⦃ Show a ⦄ → ⦃ Show b ⦄ → Show (Either a b)
  iShowEither = makeShowsPrec λ where p (Left  x) → showApp₁ p "Left"  x
                                      p (Right y) → showApp₁ p "Right" y

private
  -- Minus the parens
  showTuple : ∀ {as} → ⦃ All Show as ⦄ → Tuple as → ShowS
  showTuple             []       = showString ""
  showTuple ⦃ allCons ⦄ (x ∷ []) = shows x
  showTuple ⦃ allCons ⦄ (x ∷ xs) = shows x ∘ showString "," ∘ showTuple xs

instance
  iShowTuple : ∀ {as} → ⦃ All Show as ⦄ → Show (Tuple as)
  iShowTuple = makeShowsPrec λ _ → showParen true ∘ showTuple


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
