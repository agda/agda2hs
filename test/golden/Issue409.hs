{-# LANGUAGE RankNTypes, MultiParamTypeClasses #-}
module Issue409 where

class SUL sul where
    step :: forall i o . sul i o -> i -> (sul i o, o)
    reset :: forall i o . sul i o -> sul i o

class SUL aut => Automaton aut s where
    current :: forall i o . aut i o -> s

