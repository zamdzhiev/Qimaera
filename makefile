.PHONY: main package clean install

main:
	idris2 -p contrib -p linear Main.idr -o main

package:
	idris2 --build qimaera.ipkg

install: package
	idris2 --install qimaera.ipkg

clean:
	rm -rf build/
