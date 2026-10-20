module Issue464Instance where

import Issue464Class (Default(def), TwoMethods(methodOne, methodTwo))

data Unit = MkUnit

instance Default Unit where
    def = MkUnit

instance TwoMethods Unit where
    methodOne = MkUnit
    methodTwo = MkUnit

