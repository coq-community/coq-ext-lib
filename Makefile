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

EXTRA_DIR:=coqdocjs/extra

COQDOCFLAGS:= \
	--toc --toc-depth 1 --utf8 --interpolate --no-lib-name --parse-comments \
	--with-header $(EXTRA_DIR)/header.html \
	--with-footer $(EXTRA_DIR)/footer.html

export COQDOCFLAGS

html: Makefile.coq
	rm -rf $@
	$(MAKE) -f $< $@
	cp $(EXTRA_DIR)/resources/* $@

.PHONY: all clean dist theories examples html
