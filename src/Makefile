SHELL := /bin/bash

agda_files = $(patsubst %.agda, %.test, $(shell find . -name '*.agda'))

AGDA = agda -v 0

%.test :
	$(AGDA) $*.agda

.PHONY : test-aux
test-aux : $(agda_files)

.PHONY : test
test :
	make test-aux
	@echo "$@ succeeded!"

clean :
	rm -f *.agdai
