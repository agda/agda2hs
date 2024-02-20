
.PHONY : default clean golden alltests cubicaltests fail print-fail compare force-recompile

ROOT=$(shell cd ..; pwd)/

default : alltests cubicaltests fail compare

clean :
	@rm -rf build/*

alltests :
	@echo == Compiling tests ==
	./agda2hs AllTests.agda -o build
	@echo == Running ghc ==
	@(cd build; ghc -fno-code AllTests.hs)

cubicaltests :
	@echo == Compiling tests using cubical ==
	./agda2hs CubicalTests.agda -o build
	@echo == Running ghc ==
	@(cd build; ghc -fno-code CubicalTests.hs)

compare : fail
	@echo == Comparing output ==
	@diff -r build golden

fail : print-fail $(patsubst Fail/%.agda,build/%.err,$(wildcard Fail/*.agda))

print-fail :
	@echo == Failing tests ==

build/%.err : Fail/%.agda force-recompile alltests
	@echo Compiling $<
	@(./agda2hs $< -o build -v0 && echo "UNEXPECTED SUCCESS" || true) | sed -e 's:'$(ROOT)'::g' > $@

force-recompile :

golden :
	@cp -r build/* golden
