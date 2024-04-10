AGDA2HS=./agda2hs +RTS -M2G -RTS
ROOT=$(shell cd ..; pwd)/
MAIN=AllTests
FAIL_MAIN=AllFailTests
MAIN_RTC=AllRuntimeCheckTests

.PHONY : default allTests print-fail fail compare golden \
	html renderTranslations clean force-recompile

default : compare

build/%.hs : %.agda *.agda Fail/*.agda Cubical/*.agda agda2hs
	@echo == Compiling tests ==
	(rtc=$$(echo $< | grep RuntimeCheck); $(AGDA2HS) $${rtc:+--runtime-check} $< -o build)

allTests : build/$(MAIN).hs build/$(MAIN_RTC).hs
	@echo == Running ghc ==
	@(cd build && ghc -fno-code $(MAIN).hs && \
	              ghc -fno-code $(rtc) $(MAIN_RTC).hs)

print-fail :
	@echo == Failing tests ==
	mkdir -p build

fail : print-fail $(patsubst Fail/%.agda,build/%.err,$(wildcard Fail/*.agda))

build/%.err : Fail/%.agda agda2hs
	@echo Compiling $<
	@(rtc=$$(echo $< | grep -E '(RuntimeCheck|PostRtc)'); $(AGDA2HS) $${rtc:+--runtime-check} $< -o build -v0 \
			&& echo "UNEXPECTED SUCCESS" || true) \
		| sed -e 's:'$(ROOT)'::g' > $@

compare : allTests fail
	@echo == Comparing output ==
	@cp -r build/Haskell golden
	@diff -r build golden

golden :
	@cp -r build/* golden

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
