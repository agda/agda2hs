.PHONY : test install repl

install :
	cabal new-install --overwrite-policy=always

repl : test/*.agda
	for f in $^; do cp $${f} .; done
	cabal new-repl # e.g. `:set args AllTests.agda...main...:r...main`
	for f in $^; do f1=$${f##*/}; f2=$${f1%.*}; rm -f $${f2}.agda $${f2}.hs; done

test :
	cabal new-install --overwrite-policy=always --installdir=test --install-method=copy
	make -C test
