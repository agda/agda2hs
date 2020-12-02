
.PHONY : default clean golden alltests fail print-fail compare force-recompile

ROOT=$(shell cd ..; pwd)/

default : clean alltests fail compare

clean :
	@rm -f build/*

alltests :
	@echo == Compiling tests ==
	./agda2hs AllTests.agda -o build
	@echo == Running ghc ==
	@(cd build; ghc -fno-code AllTests.hs)

compare :
	@echo == Comparing output ==
	@diff -r build golden

fail : print-fail $(patsubst Fail/%.agda,build/%.err,$(wildcard Fail/*.agda))

print-fail :
	@echo == Failing tests ==

build/%.err : Fail/%.agda force-recompile
	@echo Compiling $<
	@(./agda2hs $< -o build -v0 && echo "UNEXPECTED SUCCESS" || true) | sed -e 's:'$(ROOT)'::g' > $@

force-recompile :

golden :
	@cp -r build/* golden
