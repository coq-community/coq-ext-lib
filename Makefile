all: theories examples

theories: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

examples: theories
	$(MAKE) -C examples

clean:
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -C examples clean

uninstall:
	$(MAKE) -f Makefile.coq uninstall


dist:
	@ git archive --prefix coq-ext-lib/ HEAD -o $(PROJECT_NAME).tgz

.PHONY: all clean dist theories examples
