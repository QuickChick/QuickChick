
.PHONY: all clean

all: Makefile.coq clean
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
