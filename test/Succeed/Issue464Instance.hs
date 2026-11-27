module Issue464Instance
  (Unit(..))
where

import Issue464Class (Default(def), Projected(projected), TwoMethods(methodOne, methodTwo))

data Unit = MkUnit

instance Default Unit where
    def = MkUnit

instance TwoMethods Unit where
    methodOne = MkUnit
    methodTwo = MkUnit

instance Projected Bool where
    projected = True

instance Projected Int where
    projected = 42

