module RuntimeCheckFeatures.PostRtc where

import Haskell.Extra.Dec.Instances (decIsFalse, decIsTrue)
import Numeric.Natural (Natural)

noneErasedFun :: Natural -> Natural
noneErasedFun _ = 1

noDecInstance :: Natural -> Natural
noDecInstance x = 0

simpleFun :: Natural -> Natural
simpleFun _ = 0

simpleFunCaller :: Natural
simpleFunCaller = simpleFun 1

singleEven :: (Natural -> Natural) -> Natural
singleEven _ = 0

doubleOdd ::
          Natural ->
            ((Natural -> Natural) -> Natural) ->
              ((Natural -> Natural) -> Natural) -> Natural
doubleOdd _ _ _ = 0

tripleOdd ::
          ((Natural -> ((Natural -> Natural) -> Natural) -> Natural) ->
             Natural)
            -> Natural
tripleOdd _ = 0

data Dat = Con Natural
         | NoneErasedCon Natural

data Rec = Rec{recFst :: Natural, recSnd :: Natural}

newtype Newt = Newt{theField :: Natural -> Natural}

newtype NoneErasedNewt = NoneErasedNewt{noneErasedField :: Natural}

data ErasedField = ErasedField{erasedFst :: Natural}

listErased :: [(Natural -> Natural) -> Natural] -> Natural
listErased _ = 0

eraseTCB :: Natural -> Natural
eraseTCB n = 0

fUnzip :: Functor f => f (a, b) -> (f a, f b)
fUnzip xs = (fmap (\ r -> fst r) xs, fmap (\ r -> snd r) xs)

