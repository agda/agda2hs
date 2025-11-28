.PHONY : build install agda repl libHtml testContainers test succeed fail golden golden-succeed golden-fail clean docs fixWhitespace checkWhitespace

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
test : checkWhitespace succeed fail testContainers

# Run only successful tests
succeed :
cabal test agda2hs-test --test-options='-p Succeed'

# Run only failing tests
fail :
cabal test agda2hs-test --test-options='-p Fail'

# Update all golden values
golden : golden-succeed golden-fail

# Update golden values for successful tests
golden-succeed :
cabal test agda2hs-test --test-options='-p Succeed --accept'

# Update golden values for failing tests
golden-fail :
cabal test agda2hs-test --test-options='-p Fail --accept'

clean :
cabal clean
rm -rf test/_build/

docs :
make -C docs html

FIXW_BIN = fix-whitespace

fixWhitespace : have-bin-$(FIXW_BIN) fix-whitespace.yaml
$(FIXW_BIN)

checkWhitespace : have-bin-$(FIXW_BIN) fix-whitespace.yaml
$(FIXW_BIN) --check

.PHONY : have-bin-%
have-bin-% :
@($* --help > /dev/null) || $(CABAL) install --ignore-project $*
