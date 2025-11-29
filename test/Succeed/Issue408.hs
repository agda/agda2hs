{-# LANGUAGE RankNTypes, QuantifiedConstraints #-}
module Issue408 where

class SUL sul where
    step :: forall i o . sul i o -> i -> (sul i o, o)
    reset :: forall i o . sul i o -> sul i o

class (forall s . SUL (aut s)) => Automaton aut where
    current :: forall s i o . aut s i o -> s

