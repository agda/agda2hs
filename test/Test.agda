module _ where

open import Haskell.Prelude
open import Agda.Builtin.Equality

-- ** Foreign HS code

-- language extensions
{-# FOREIGN AGDA2HS
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
#-}

-- imports
{-# FOREIGN AGDA2HS
import Data.Monoid
#-}

-- ** Datatypes & functions

data Exp (v : Set) : Set where
  Plus : Exp v → Exp v → Exp v
  Lit : Nat → Exp v
  Var : v → Exp v
{-# COMPILE AGDA2HS Exp deriving (Show,Eq) #-}

eval : (a → Nat) → Exp a → Nat
eval env (Plus a b) = eval env a + eval env b
eval env (Lit n) = n
eval env (Var x) = env x
{-# COMPILE AGDA2HS eval #-}

-- ** Natural numbers

listSum : List Int → Int
listSum []       = 0
listSum (x ∷ xs) = x + sum xs
{-# COMPILE AGDA2HS listSum #-}

monoSum : List Integer → Integer
monoSum xs = sum xs
{-# COMPILE AGDA2HS monoSum #-}

polySum : ⦃ iNum : Num a ⦄ → List a → a
polySum xs = sum xs
{-# COMPILE AGDA2HS polySum #-}

{-# FOREIGN AGDA2HS
-- comment
-- another comment
bla :: Int -> Int
bla n = n * 4

{- multi
   line
   comment
-}
#-}

-- ** Extra builtins

ex_float : Double
ex_float = 0.0
{-# COMPILE AGDA2HS ex_float #-}

postulate
  toInteger : Word → Integer

ex_word : Word
ex_word = fromInteger 0
{-# COMPILE AGDA2HS ex_word #-}

ex_char : Char
ex_char = 'a'
{-# COMPILE AGDA2HS ex_char #-}

char_d : Char
char_d = toEnum 100
{-# COMPILE AGDA2HS char_d #-}

-- ** Polymorphic functions

_+++_ : List a → List a → List a
[]       +++ ys = ys
(x ∷ xs) +++ ys = x ∷ (xs +++ ys)
{-# COMPILE AGDA2HS _+++_ #-}

listMap : (a → b) → List a → List b
listMap f [] = []
listMap f (x ∷ xs) = f x ∷ listMap f xs
{-# COMPILE AGDA2HS listMap #-}

mapTest : List Nat → List Nat
mapTest = map (id ∘ _+_ 5)
{-# COMPILE AGDA2HS mapTest #-}

-- ** Lambdas

plus3 : List Nat → List Nat
plus3 = map (λ n → n + 3)
{-# COMPILE AGDA2HS plus3 #-}

doubleLambda : Nat → Nat → Nat
doubleLambda = λ a b → a + 2 * b
{-# COMPILE AGDA2HS doubleLambda #-}

cnst : a → b → a
cnst = λ x _ → x
{-# COMPILE AGDA2HS cnst #-}

-- ** Constraints

second : (b → c) → a × b → a × c
second f (x , y) = x , f y
{-# COMPILE AGDA2HS second #-}

doubleTake : (n m : Int) → ⦃ IsNonNegativeInt n ⦄ → ⦃ IsNonNegativeInt m ⦄ → List a → List a × List a
doubleTake n m = second (take m) ∘ splitAt n
{-# COMPILE AGDA2HS doubleTake #-}

initLast : (xs : List a) → ⦃ NonEmpty xs ⦄ → List a × a
initLast xs = init xs , last xs
{-# COMPILE AGDA2HS initLast #-}

-- ** Proofs

assoc : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
assoc zero    b c = refl
assoc (suc a) b c rewrite assoc a b c = refl

thm : (xs ys : List Nat) → sum (xs ++ ys) ≡ sum xs + sum ys
thm []       ys = refl
thm (x ∷ xs) ys rewrite thm xs ys | assoc x (sum xs) (sum ys) = refl

-- (custom) Monoid class

record MonoidX (a : Set) : Set where
  field memptyX  : a
        mappendX : a → a → a

open MonoidX {{...}} public

{-# COMPILE AGDA2HS MonoidX class #-}

instance
  MonoidNat : MonoidX Nat
  memptyX  {{MonoidNat}}     = 0
  mappendX {{MonoidNat}} i j = i + j

{-# COMPILE AGDA2HS MonoidNat #-}


instance
  MonoidFunNat : {a : Set} → MonoidX (a → Nat)
  memptyX  {{MonoidFunNat}}     _ = memptyX
  mappendX {{MonoidFunNat}} f g x = mappendX (f x) (g x)

{-# COMPILE AGDA2HS MonoidFunNat #-}

instance
  MonoidFun : {a b : Set} → {{MonoidX b}} → MonoidX (a → b)
  memptyX  {{MonoidFun}}     _ = memptyX
  mappendX {{MonoidFun}} f g x = mappendX (f x) (g x)
{-# COMPILE AGDA2HS MonoidFun #-}

sumMonX : ∀{a} → {{MonoidX a}} → List a → a
sumMonX []       = memptyX
sumMonX (x ∷ xs) = mappendX x (sumMonX xs)
{-# COMPILE AGDA2HS sumMonX #-}

sumMon : ∀{a} → {{Monoid a}} → List a → a
sumMon []       = mempty
sumMon (x ∷ xs) = x <> sumMon xs
{-# COMPILE AGDA2HS sumMon #-}

-- Using the Monoid class from the Prelude

data NatSum : Set where
  MkSum : Nat → NatSum

{-# COMPILE AGDA2HS NatSum #-}

instance
  SemigroupNatSum : Semigroup NatSum
  SemigroupNatSum ._<>_ (MkSum a) (MkSum b) = MkSum (a + b)

  MonoidNatSum : Monoid NatSum
  MonoidNatSum .mempty = MkSum 0

double : ⦃ Monoid a ⦄ → a → a
double x = x <> x

doubleSum : NatSum → NatSum
doubleSum = double

{-# COMPILE AGDA2HS SemigroupNatSum #-}
{-# COMPILE AGDA2HS MonoidNatSum    #-}
{-# COMPILE AGDA2HS double          #-}
{-# COMPILE AGDA2HS doubleSum       #-}

-- Instance argument proof obligation that should not turn into a class constraint
hd : (xs : List a) → ⦃ NonEmpty xs ⦄ → a
hd []      = error "hd: empty list"
hd (x ∷ _) = x
{-# COMPILE AGDA2HS hd #-}

five : Int
five = hd (5 ∷ 3 ∷ [])
{-# COMPILE AGDA2HS five #-}

-- ** Booleans

ex_bool : Bool
ex_bool = true
{-# COMPILE AGDA2HS ex_bool #-}

ex_if : Nat
ex_if = if true then 1 else 0
{-# COMPILE AGDA2HS ex_if #-}

if_over : Nat
if_over = (if true then (λ x → x) else (λ x → x + 1)) 0
{-# COMPILE AGDA2HS if_over #-}

if_partial₁ : List Nat → List Nat
if_partial₁ = map (if true then 1 else_)
{-# COMPILE AGDA2HS if_partial₁ #-}

if_partial₂ : List Nat → List (Nat → Nat)
if_partial₂ = map (if true then_else_)
{-# COMPILE AGDA2HS if_partial₂ #-}

if_partial₃ : List Bool → List (Nat → Nat → Nat)
if_partial₃ = map if_then_else_
{-# COMPILE AGDA2HS if_partial₃ #-}

if_partial₄ : List Bool → List (Nat → Nat)
if_partial₄ = map (if_then 1 else_)
{-# COMPILE AGDA2HS if_partial₄ #-}

if_partial₅ : Bool → Nat → List Nat → List Nat
if_partial₅ b f = map (if b then f else_)
{-# COMPILE AGDA2HS if_partial₅ #-}
