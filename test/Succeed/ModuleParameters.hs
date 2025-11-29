{-# LANGUAGE ScopedTypeVariables #-}
module ModuleParameters where

data Scope p = Empty
             | Bind p (Scope p)

unbind :: forall p . Scope p -> Scope p
unbind Empty = Empty
unbind (Bind _ s) = s

thing :: forall p a . a -> a
thing x = y
  where
    y :: a
    y = x

stuff :: forall p a . a -> Scope p -> a
stuff x Empty = x
stuff x (Bind _ _) = x

more :: forall p a b . b -> a -> Scope p -> Scope p
more _ _ Empty = Empty
more _ _ (Bind _ s) = s

