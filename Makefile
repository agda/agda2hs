.PHONY : test install repl agda

install :
	cabal new-install --overwrite-policy=always

agda :
	cabal new-install Agda --program-suffix=-erased --overwrite-policy=always

repl :
	cabal new-repl # e.g. `:set args -itest -otest/build test/AllTests.agda ... main ... :r ... main`

test :
	cabal new-install agda2hs --overwrite-policy=always --installdir=test --install-method=copy
	make -C test

golden :
	make -C test golden

docs :
	cd docs && make html
