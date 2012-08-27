TESTS      := 
MONAD      := $(patsubst %.v,%,$(wildcard Monad/*.v))
TACTICS    := $(patsubst %.v,%,$(wildcard Tactics/*.v))
DATA       := $(patsubst %.v,%,$(wildcard Data/*.v))
DECIDABLES := $(patsubst %.v,%,$(wildcard Decidables/*.v))
WITH       := $(patsubst %.v,%,$(wildcard With/*.v))
RELATIONS  := $(patsubst %.v,%,$(wildcard Relations/*.v))
MODULES    := $(TACTICS) $(MONAD) $(DATA) $(DECIDABLES) $(WITH) $(RELATIONS)
VS         := $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS :=-R . ExtLib

.PHONY: coq clean admit depgraph toplevel

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) -o Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq

test: coq Makefile.test.coq
	$(MAKE) -f Makefile.test.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend 

admit:
	@ grep -n -e 'admit' -e 'Admitted' ${VS}

depgraph: Makefile.coq
	@ echo Generating dependency graph to ../deps.pdf
	@ ./../tools/deps.py $(MODULES:%=%.v.d) > ../deps.dot
	@ ./../tools/deps.py $(MODULES:%=%.v.d) | dot -Tpdf -o ../deps.pdf

toplevel: coq
	coqtop.opt $(ARGS)