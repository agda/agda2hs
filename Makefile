.PHONY : install agda repl libHtml testContainers test test-on-CI testHtml golden clean docs
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

test : checkWhitespace test-on-CI

test-on-CI : test/agda2hs testContainers
	make -C test

testHtml : test/agda2hs
	make -C test html

golden :
	make -C test golden

clean :
	make -C test clean

docs :
	make -C docs html

FIXW_BIN = fix-whitespace

.PHONY : fixWhitespace ## Fix the whitespace issue.
fixWhitespace : have-bin-$(FIXW_BIN) fix-whitespace.yaml
	$(FIXW_BIN)

.PHONY : checkWhitespace ## Check the whitespace issue without fixing it.
checkWhitespace : have-bin-$(FIXW_BIN) fix-whitespace.yaml
	$(FIXW_BIN) --check

.PHONY : have-bin-% ## Installing binaries for developer services
have-bin-% :
	@($* --help > /dev/null) || $(CABAL) install --ignore-project $*
