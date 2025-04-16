module Haskell.Law.Num.Int where

open import Haskell.Prim using (refl; tt)
open import Haskell.Prim.Num
open import Haskell.Prim.Int
open import Haskell.Prim.Word

open import Haskell.Law.Num.Def
open import Haskell.Law.Num.Word

instance
  open NumHomomorphism
  open NumEmbedding

  iNumEmbeddingIntWord : NumEmbedding Int Word intToWord int64
  +-hom          (hom iNumEmbeddingIntWord) (int64 _) (int64 _) = refl
  *-hom          (hom iNumEmbeddingIntWord) (int64 _) (int64 _) = refl
  minus-ok       (hom iNumEmbeddingIntWord) = tt
  negate-ok      (hom iNumEmbeddingIntWord) = tt
  fromInteger-ok (hom iNumEmbeddingIntWord) = tt
  0-hom          (hom iNumEmbeddingIntWord) = refl
  1-hom          (hom iNumEmbeddingIntWord) = refl
  negate-hom     (hom iNumEmbeddingIntWord) (int64 _) = refl
  embed               iNumEmbeddingIntWord  (int64 _) = refl

  iLawfulNumInt : IsLawfulNum Int
  iLawfulNumInt = map-IsLawfulNum intToWord int64 iNumEmbeddingIntWord iLawfulNumWord
