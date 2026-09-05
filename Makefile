COQMAKEFILE ?= coq_makefile

all: Makefile.coq
	$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject DeBruijn.v
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq

clean:
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean
