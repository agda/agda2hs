
AGDA2HS=$(shell cabal -v0 exec -- which -- agda2hs)

.PHONY : test install

install :
	cabal install

test :
	@AGDA2HS=$(AGDA2HS) make -C test
