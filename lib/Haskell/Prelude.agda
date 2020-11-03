{-# OPTIONS --no-auto-inline #-}
module Haskell.Prelude where

open import Agda.Builtin.Unit  public
open import Agda.Builtin.List  public
open import Agda.Builtin.Nat   public
open import Agda.Builtin.Bool  public
open import Agda.Builtin.Float public
open import Agda.Builtin.Char  public

-- Type variables --

variable
  a b c d e f g h i j k l m n o p q r s t u v w x y z : Set

-- Functions --

id : a → a
id x = x

infixr 9 _∘_
_∘_ : (b → c) → (a → b) → a → c
(f ∘ g) x = f (g x)

flip : (a → b → c) → b → a → c
flip f x y = f y x

-- Tuples --

infixr 5 _∷_
data Tuple : List Set → Set where
  []  : Tuple []
  _∷_ : ∀ {as} → a → Tuple as → Tuple (a ∷ as)

⟨_×_⟩ : (a b : Set) → Set
⟨ a × b ⟩ = Tuple (a ∷ b ∷ [])

⟨_×_×_⟩ : (a b c : Set) → Set
⟨ a × b × c ⟩ = Tuple (a ∷ b ∷ c ∷ [])

pattern ⟨_,_⟩   x y   = x Tuple.∷ y Tuple.∷ []
pattern ⟨_,_,_⟩ x y z = x Tuple.∷ y Tuple.∷ z Tuple.∷ []

uncurry : (a → b → c) → ⟨ a × b ⟩ → c
uncurry f ⟨ x , y ⟩ = f x y

curry : (⟨ a × b ⟩ → c) → a → b → c
curry f x y = f ⟨ x , y ⟩

-- Booleans --

infix 0 if_then_else_
if_then_else_ : Bool → a → a → a
if true  then t else f = t
if false then t else f = f

-- Maybe --

data Maybe (a : Set) : Set where
  Nothing : Maybe a
  Just    : a -> Maybe a
