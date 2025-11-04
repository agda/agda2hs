module ErasedPatternLambda where

data Telescope = ExtendTel Bool Telescope

caseTelBind :: Telescope -> (Bool -> Telescope -> d) -> d
caseTelBind (ExtendTel a tel) f = f a tel

checkSubst :: Telescope -> Bool
checkSubst t = caseTelBind t (\ ty rest -> True)

