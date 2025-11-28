module RelevantDotPattern3 where

data Telescope = ExtendTel Bool Telescope

caseTelBind :: Telescope -> (Bool -> Telescope -> d) -> d
caseTelBind (ExtendTel a tel) f = f a tel

checkSubst' :: Telescope -> Bool -> Telescope -> Bool
checkSubst' (ExtendTel ty' rest') ty rest = True

checkSubst :: Telescope -> Bool
checkSubst t = caseTelBind t (checkSubst' t)

