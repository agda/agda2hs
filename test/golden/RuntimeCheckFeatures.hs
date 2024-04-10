module RuntimeCheckFeatures (noneErasedFun, simpleFunCaller, singleEven, Dat(NoneErasedCon), Rec(recFst, recSnd), Newt(theField), NoneErasedNewt(noneErasedField, NoneErasedNewt), ErasedField(erasedFst), fUnzip, RuntimeCheckFeatures.simpleFun, RuntimeCheckFeatures.doubleOdd, RuntimeCheckFeatures.tripleOdd, RuntimeCheckFeatures.scCon, RuntimeCheckFeatures.scRec, RuntimeCheckFeatures.scNewt, RuntimeCheckFeatures.scErasedField) where

import Haskell.Extra.Dec.Instances (decIsFalse, decIsTrue)
import Numeric.Natural (Natural)

import RuntimeCheckFeatures.PostRtc

simpleFun :: Natural -> Natural
simpleFun x
  | decIsTrue (x > 0) = RuntimeCheckFeatures.PostRtc.simpleFun x
  | otherwise = error "Runtime check failed: decIsTrue (x > 0)"

doubleOdd ::
          Natural ->
            ((Natural -> Natural) -> Natural) ->
              ((Natural -> Natural) -> Natural) -> Natural
doubleOdd x a0 a2
  = RuntimeCheckFeatures.PostRtc.doubleOdd x (\ a1 -> a0 (go0 a1))
      (\ a3 -> a2 (go1 a3))
  where
    go0 up y
      | decIsFalse (x < y) = up y
      | otherwise = error "Runtime check failed: decIsFalse (x < y)"
    go1 up y
      | decIsFalse (x < y) = up y
      | otherwise = error "Runtime check failed: decIsFalse (x < y)"

tripleOdd ::
          ((Natural -> ((Natural -> Natural) -> Natural) -> Natural) ->
             Natural)
            -> Natural
tripleOdd a0
  = RuntimeCheckFeatures.PostRtc.tripleOdd (\ a1 -> a0 (go1 a1))
  where
    go1 up m a2
      | decIsTrue (m > 0) = up m (\ a3 -> a2 (go0 a3))
      | otherwise = error "Runtime check failed: decIsTrue (m > 0)"
      where
        go0 up n
          | decIsFalse (n < 1) = up n
          | otherwise = error "Runtime check failed: decIsFalse (n < 1)"

scCon :: Natural -> Dat
scCon x
  | decIsTrue (x > 0) = Con x
  | otherwise = error "Runtime check failed: decIsTrue (x > 0)"

scRec :: Natural -> Natural -> Rec
scRec recFst recSnd = Rec recFst (go0 recSnd)
  where
    go0 up
      | decIsTrue (recFst > 0) = up
      | otherwise = error "Runtime check failed: decIsTrue (recFst > 0)"

scNewt :: (Natural -> Natural) -> Newt
scNewt theField = Newt (go0 theField)
  where
    go0 up x
      | decIsTrue (x > 0) = up x
      | otherwise = error "Runtime check failed: decIsTrue (x > 0)"

scErasedField :: Natural -> ErasedField
scErasedField erasedFst
  | decIsTrue (erasedFst > 0) = ErasedField erasedFst
  | otherwise =
    error "Runtime check failed: decIsTrue (erasedFst > 0)"

