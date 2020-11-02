module Issue14 where

constid :: a -> b -> b
constid x = \ x -> x

sectionTest₁ :: Integer -> Integer -> Integer
sectionTest₁ n = \ section -> section + n

sectionTest₂ :: Integer -> Integer -> Integer
sectionTest₂ section = \ section -> section + section₁

