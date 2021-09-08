module Issue73 where

record ImplicitField (a : Set) : Set where
    field
        aField : a
        {anImplicitField} : a
open ImplicitField public
{-# COMPILE AGDA2HS ImplicitField class #-}
