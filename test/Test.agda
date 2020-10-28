module _ where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
-- open import Agda.Builtin.Float
-- open import Agda.Builtin.Word
-- open import Agda.Builtin.Char
open import Agda.Builtin.Equality

variable
  a b : Set

-- ** Foreign HS code

-- language extensions
{-# FOREIGN AGDA2HS
{-# LANGUAGE LambdaCase #-}
#-}

-- imports
{-# FOREIGN AGDA2HS
import Prelude hiding (map, sum, (++))
import Data.Monoid
import Data.Word
#-}

-- ** Datatypes & functions

data Exp (v : Set) : Set where
  Plus : Exp v → Exp v → Exp v
  Int : Nat → Exp v
  Var : v → Exp v
{-# COMPILE AGDA2HS Exp #-}

eval : (a → Nat) → Exp a → Nat
eval env (Plus a b) = eval env a + eval env b
eval env (Int n) = n
eval env (Var x) = env x
{-# COMPILE AGDA2HS eval #-}

-- ** Natural numbers

sum : List Nat → Nat
sum []       = 0
sum (x ∷ xs) = x + sum xs
{-# COMPILE AGDA2HS sum #-}

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

-- floats
postulate Float : Set
{-# BUILTIN FLOAT Float #-}

ex_float : Float
ex_float = 0.0
{-# COMPILE AGDA2HS ex_float #-}

primitive
  primFloatPlus : Float -> Float -> Float
  -- TODO more primitives
{-# COMPILE AGDA2HS primFloatPlus #-}

sumF : List Float → Float
sumF []       = 0.0
sumF (x ∷ xs) = primFloatPlus x (sumF xs)
{-# COMPILE AGDA2HS sumF #-}

-- words
postulate Word64 : Set
{-# BUILTIN WORD64 Word64 #-}

primitive
  primWord64FromNat : Nat → Word64
  primWord64ToNat : Word64 → Nat
{-# COMPILE AGDA2HS primWord64FromNat = fromIntegral #-}
{-# COMPILE AGDA2HS primWord64ToNat #-}

ex_word : Word64
ex_word = primWord64FromNat 0
{-# COMPILE AGDA2HS ex_word #-}

ex_nat : Nat
ex_nat = primWord64ToNat ex_word
{-# COMPILE AGDA2HS ex_nat #-}

-- chars
postulate Char : Set
{-# BUILTIN CHAR Char #-}

primitive
  primCharToNat : Char → Nat
  primNatToChar : Nat → Char
  -- TODO more primitives
{-# COMPILE AGDA2HS primCharToNat #-}
{-# COMPILE AGDA2HS primNatToChar #-}

ex_char : Char
ex_char = 'a'
{-# COMPILE AGDA2HS ex_char #-}

toN : Char -> Nat
toN = primCharToNat
{-# COMPILE AGDA2HS toN #-}

-- ** Polymorphic functions

_++_ : List a → List a → List a
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
{-# COMPILE AGDA2HS _++_ #-}

map : (a → b) → List a → List b
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs
{-# COMPILE AGDA2HS map #-}

-- ** Lambdas

plus3 : List Nat → List Nat
plus3 = map (λ n → n + 3)
{-# COMPILE AGDA2HS plus3 #-}

doubleLambda : Nat → Nat → Nat
doubleLambda = λ a b → a + 2 * b
{-# COMPILE AGDA2HS doubleLambda #-}

-- ** Proofs

assoc : (a b c : Nat) → a + (b + c) ≡ (a + b) + c
assoc zero    b c = refl
assoc (suc a) b c rewrite assoc a b c = refl

thm : ∀ xs ys → sum (xs ++ ys) ≡ sum xs + sum ys
thm []       ys = refl
thm (x ∷ xs) ys rewrite thm xs ys | assoc x (sum xs) (sum ys) = refl

