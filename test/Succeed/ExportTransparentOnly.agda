module ExportTransparentOnly where

myId : {A : Set} → A → A
myId x = x
{-# COMPILE AGDA2HS myId transparent #-}
