
.PHONY : default golden

default :
	@echo == Compiling tests ==
	./agda2hs AllTests.agda -o build
	@echo == Running ghc ==
	@(cd build; ghc AllTests.hs)
	@find build \( -name '*.o' -o -name '*.hi' \) -exec rm {} \;
	@echo == Comparing output ==
	@diff -r -x '*.hi' -x '*.o' build golden

golden :
	@cp -r build/* golden
