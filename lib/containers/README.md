`containers.agda-lib` proves properties about the Haskell [containers][] library.


## Roadmap

For the time being, this library is developed as part of the [agda2hs][] repository. There are two reasons:

* Significant backflow of code from `containers.agda-lib` to `base.agda-lib`. For example, proving properties about `Data.Map.spanAntitone` will require additions to `Data.Ord`.
* Informs the development of [agda2hs][]: changes to `agda2hs` are immediately confronted with the fact that there is at least one separate library of considerable size.

However, once [agda2hs][] has become sufficiently complete and stable, we want to move `containers.agda-lib` into a separate repository.

  [agda2hs]: https://github.com/agda/agda2hs
  [containers]: https://hackage.haskell.org/package/containers
