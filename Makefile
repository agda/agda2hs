
.PHONY : test install

install :
	cabal new-install --overwrite-policy=always

test :
	@make -C test
