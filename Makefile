.PHONY : test install repl agda

install :
	cabal install --overwrite-policy=always

agda :
	cabal install Agda --program-suffix=-erased --overwrite-policy=always

repl :
	cabal repl # e.g. `:set args -itest -otest/build test/AllTests.agda ... main ... :r ... main`

test :
	cabal install agda2hs --overwrite-policy=always --installdir=test --install-method=copy
	make -C test

libHtml :
	cabal run agda2hs -- --html lib/Haskell/Prelude.agda
	cp html/Haskell.Prelude.html html/index.html

golden :
	make -C test golden

docs :
	cd docs && make html
