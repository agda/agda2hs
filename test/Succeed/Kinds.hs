module Kinds
  (ReaderT(..), Kleisli(..))
where

data ReaderT r m a = RdrT{runReaderT :: r -> m a}

data Kleisli m a b = K (a -> m b)

