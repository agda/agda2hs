AGDA2HS=./agda2hs +RTS -M2G -RTS
ROOT=$(shell cd ..; pwd)/
MAIN=AllTests
FAIL_MAIN=AllFailTests

.PHONY : default allTests print-fail fail compare golden \
	html renderTranslations clean force-recompile

default : compare

build/%.hs : %.agda *.agda Fail/*.agda Cubical/*.agda agda2hs
	@echo == Compiling tests ==
	$(AGDA2HS) $< -o build

allTests : build/$(MAIN).hs
	@echo == Running ghc ==
	@(cd build && ghc -fno-code $(MAIN).hs)

print-fail :
	@echo == Failing tests ==

fail : print-fail $(patsubst Fail/%.agda,build/%.err,$(wildcard Fail/*.agda))

build/%.err : Fail/%.agda agda2hs
	@echo Compiling $<
	@($(AGDA2HS) $< -o build -v0 && echo "UNEXPECTED SUCCESS" || true) | sed -e 's:'$(ROOT)'::g' > $@

compare : allTests fail
	@echo == Comparing output ==
	@diff -r build golden

golden :
	@cp build/*.hs build/Cubical/*.hs build/*.err golden

html : allTests fail html/index.html html/fail/index.html renderTranslations

html/index.html : html/$(MAIN).html
	echo "<meta http-equiv=\"refresh\" content=\"0; url=$(MAIN).html\" />" > $@

html/fail/index.html : html/$(FAIL_MAIN).html
	mkdir -p html/fail/
	echo "<meta http-equiv=\"refresh\" content=\"0; url=../$(FAIL_MAIN).html\" />" > $@

html/Agda.css : Agda.css
	mkdir -p html/
	cp -f $< $@

html/%.html : %.agda html/Agda.css renderTranslations.sh
	@echo == Generating test-suite HTML ==
	$(AGDA2HS) -d --html --css=Agda.css $<

html/$(FAIL_MAIN).html : renderTranslations.sh
	@echo == Generating failing test-suite HTML ==
	$(AGDA2HS) -d --html --css=Agda.css $(FAIL_MAIN).agda

renderTranslations : html/index.html html/fail/index.html renderTranslations.sh
	./renderTranslations.sh

clean :
	@rm -rf _build/ build/ html/

force-recompile :
