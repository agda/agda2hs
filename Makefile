.PHONY : install agda repl libHtml test testHtml golden docs
FILES = $(shell find src -type f)

install :
	cabal install --overwrite-policy=always

agda :
	cabal install Agda --program-suffix=-erased --overwrite-policy=always

repl :
	cabal repl # e.g. `:set args -itest -otest/build test/AllTests.agda ... main ... :r ... main`

libHtml :
	cabal run agda2hs -- --html --include-path lib/base lib/base/Haskell/Prelude.agda
	cp html/Haskell.Prelude.html html/index.html

test/agda2hs : $(FILES)
	cabal install agda2hs --overwrite-policy=always --installdir=test --install-method=copy

test : test/agda2hs
	make -C test

testHtml : test/agda2hs
	make -C test html

golden :
	make -C test golden

docs :
	make -C docs html
