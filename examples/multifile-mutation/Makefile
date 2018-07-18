all: Makefile.coq 
	$(MAKE) -f Makefile.coq 

Makefile.coq: 
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf ../_qc_multifile-mutation.tmp *.bak

test: clean
	time quickChick -color
	-quickChick -color -include _CoqProject
