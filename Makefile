PROJECT_NAM=coq-ext-lib

all:
	$(MAKE) -C theories

clean:
	$(MAKE) -C theories clean

dist:
	@ git archive HEAD -o $(PROJECT_NAME).tgz

.dir-locals.el: tools/dir-locals.el
	@ sed s,PWD,$(shell pwd -P),g tools/dir-locals.el > .dir-locals.el

.PHONY: all clean dist
