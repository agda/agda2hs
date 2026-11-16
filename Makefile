.PHONY : build install agda repl libHtml testContainers test succeed fail custom golden golden-succeed golden-fail golden-custom clean docs fixWhitespace checkWhitespace have-bin-%

FILES = $(shell find src -type f)

build :
	cabal build

install :
	cabal install --overwrite-policy=always

agda :
	cabal install Agda --program-suffix=-erased --overwrite-policy=always

repl :
	cabal repl

libHtml :
	cabal run agda2hs -- --html --include-path lib/base lib/base/Haskell/Prelude.agda
	cp html/Haskell.Prelude.html html/index.html

testContainers:
	cd ./lib/containers && ./generate-haskell.sh && cabal build containers-prop

# Run all tests
test : checkWhitespace test-on-CI

# Run all tests except for fix-whitespace
test-on-CI : succeed fail custom testContainers

# The trailing dot in the test patterns selects a test group exactly, so that
# e.g. a "SucceedFoo" test in another group is not matched. --no-create makes
# missing goldens fail validation.

# Run only successful tests
succeed :
	cabal test agda2hs-test --test-options='-p Succeed. --no-create'

# Run only failing tests
fail :
	cabal test agda2hs-test --test-options='-p Fail. --no-create'

# Run only custom tests
custom :
	cabal test agda2hs-test --test-options='-p Custom. --no-create'

# Update all golden values
golden : golden-succeed golden-fail golden-custom

# Update golden values for successful tests
golden-succeed :
	cabal test agda2hs-test --test-options='-p Succeed. --accept'

# Update golden values for failing tests
golden-fail :
	cabal test agda2hs-test --test-options='-p Fail. --accept'

# Update golden values for custom tests
golden-custom :
	cabal test agda2hs-test --test-options='-p Custom. --accept'

clean :
	cabal clean
	rm -rf test/_build/

docs :
	make -C docs html

FIXW_BIN = fix-whitespace

## Fix the whitespace issue.
fixWhitespace : have-bin-$(FIXW_BIN) fix-whitespace.yaml
	$(FIXW_BIN)

## Check the whitespace issue without fixing it.
checkWhitespace : have-bin-$(FIXW_BIN) fix-whitespace.yaml
	$(FIXW_BIN) --check

## Installing binaries for developer services
have-bin-% :
	@($* --help > /dev/null) || $(CABAL) install --ignore-project $*
