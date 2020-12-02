.PHONY : test install repl

install :
	cabal new-install --overwrite-policy=always

repl :
	cabal new-repl # e.g. `:set args -itest -otest/build test/AllTests.agda ... main ... :r ... main`

test :
	cabal new-install --overwrite-policy=always --installdir=test --install-method=copy
	make -C test

golden :
	make -C test golden
