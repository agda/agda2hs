module ExportList
  (publicFun, publicFun2, PublicTy, PublicData(..), PublicNewtype(..), PublicRecord(..), PublicClass(..), llength)
where

import Numeric.Natural (Natural)
import qualified Prelude (Num((+)))

publicFun :: a -> a
publicFun x = x

privateFun :: a -> a
privateFun x = x

publicFun2 :: a -> a
publicFun2 x = x

privateFun2 :: a -> a
privateFun2 x = x

privateFun3 :: a -> a
privateFun3 x = x

type PublicTy = Natural

type PrivateTy = Natural

data PublicData = MkPublicData

data PrivateData = MkPrivateData

newtype PublicNewtype = MkPublicNewtype Natural

newtype PrivateNewtype = MkPrivateNewtype Natural

data PublicRecord = MkPublicRecord{publicField :: Natural}

class PublicClass where
    publicMethod :: Natural

llength :: [a] -> Natural
llength [] = 0
llength (x : xs) = (Prelude.+) 1 (llength xs)

