module LawfulOrd where

data Ordered a = Gt a a
               | Lt a a
               | E a a

