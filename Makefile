.PHONY : install agda repl libHtml test testContainers testHtml golden docs
FILES = $(shell find src -type f)

build :
	cabal build

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

testContainers:
	cd ./lib/containers && ./generate-haskell.sh && cabal build containers-prop

test : test/agda2hs testContainers
	make -C test

testHtml : test/agda2hs
	make -C test html

golden :
	make -C test golden

clean :
	make -C test clean

docs :
	make -C docs html
