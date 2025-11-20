module Issue443
  (test)
where

test :: ()
test = local
  where
    local :: ()
    local = error "postulate: ()"

