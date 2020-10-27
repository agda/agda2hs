
.PHONY : test install

install :
	cabal new-install --overwrite-policy=always

test :
	cabal new-install --overwrite-policy=always --installdir=test --install-method=copy
	make -C test
