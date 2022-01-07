.PHONY : build install run repl tui test golden

build :
	cabal new-build

install :
	cabal new-install --overwrite-policy=always

run :
	cabal new-run

repl :
	cabal new-repl # e.g. `:set args -itest -otest/build test/AllTests.agda ... main ... :r ... main`

tui :
	cabal new-run tui

test :
	cabal new-install --overwrite-policy=always --installdir=test --install-method=copy
	make -C test

golden :
	make -C test golden
