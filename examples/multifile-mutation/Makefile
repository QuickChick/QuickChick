all: Makefile.coq 
	$(MAKE) -f Makefile.coq 
	quickChick .

Makefile.coq: 
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -f Makefile.coq clean
	rm -rf _qc *.bak

