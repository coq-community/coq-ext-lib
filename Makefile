all: theories examples

-include coqdocjs/Makefile.doc
COQMAKEFILE?=Makefile.coq

theories: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE):
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

install: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) install

examples: theories
	$(MAKE) -C examples

clean:
	if [ -e $(COQMAKEFILE) ] ; then $(MAKE) -f $(COQMAKEFILE) cleanall ; fi
	$(MAKE) -C examples clean
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

uninstall:
	$(MAKE) -f $(COQMAKEFILE) uninstall

dist:
	@ git archive --prefix coq-ext-lib/ HEAD -o $(PROJECT_NAME).tgz

.PHONY: all clean dist theories examples html

TEMPLATES ?= ../templates

docs/index.html: index.md
	pandoc -s $^ -o $@

index.md: meta.yml
	$(TEMPLATES)/generate.sh $@
