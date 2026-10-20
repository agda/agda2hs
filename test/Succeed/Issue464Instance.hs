module Issue464Instance where

import Issue464Class (Default(def))

data Unit = MkUnit

instance Default Unit where
    def = MkUnit

