build:
	stack build

install:
	stack install

test:
	stack test

doc:
	stack haddock --open

format:
	ormolu --mode inplace $$(find . -name '*.hs')

eval:
	./test/eval.sh

clean:
	stack clean

.PHONY: build install test doc format eval clean
.SILENT:
