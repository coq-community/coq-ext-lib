all: theories examples

theories: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

examples: theories
	$(MAKE) -C examples

clean:
	if [ -e Makefile.coq ] ; then $(MAKE) -f Makefile.coq cleanall ; fi
	$(MAKE) -C examples clean
	@rm -f Makefile.coq Makefile.coq.conf

uninstall:
	$(MAKE) -f Makefile.coq uninstall


dist:
	@ git archive --prefix coq-ext-lib/ HEAD -o $(PROJECT_NAME).tgz

include tools/Makefile.doc

%.md: meta.yml templates/%.md.mustache
	mustache $^ > $@

%.html: %.md
	pandoc -s -o $@ $<

.PHONY: all clean dist theories examples html
