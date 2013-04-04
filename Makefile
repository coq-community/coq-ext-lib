PROJECT_NAME=coq-ext-lib

all: theories examples

theories:
	$(MAKE) -C theories

install:
	$(MAKE) -C theories install

examples: theories
	$(MAKE) -C examples

clean:
	$(MAKE) -C theories clean
	$(MAKE) -C examples clean

dist:
	@ git archive HEAD -o $(PROJECT_NAME).tgz

.dir-locals.el: tools/dir-locals.el
	@ sed s,PWD,$(shell pwd -P),g tools/dir-locals.el > .dir-locals.el

.PHONY: all clean dist theories examples
