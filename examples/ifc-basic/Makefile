
.PHONY: all clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq
