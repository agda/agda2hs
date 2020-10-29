
.PHONY : default golden

default :
	@echo == Compiling tests ==
	./agda2hs AllTests.agda -o build
	@echo == Running ghc ==
	@(cd build; ghc -fno-code AllTests.hs)
	@echo == Comparing output ==
	@diff -r build golden

golden :
	@cp -r build/* golden
