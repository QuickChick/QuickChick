QC=quickChick -color -ocamlbuild '-lib unix -no-hygiene'
TMP_DIR=../_qc_$(shell basename $CURDIR).tmp
all: Makefile.coq extract.cmxs
	$(MAKE) -f $<

test:
	time $(QC)

lesstest:
	time $(QC) -N 100

Makefile.coq: _CoqProject
	coq_makefile -o $@ -f $<

%.o: %.c
	ocamlc -c $<

libcamlplus.a: camlplus.o cplus.o
	ocamlmklib -custom -o camlplus $^

extract.cmxs: extract.ml libcamlplus.a
	ocamlopt -shared -o $@ $< -cclib -lcamlplus -ccopt -L.

testextract.out: extract.ml testextract.ml libcamlplus.a
	ocamlopt -o $@ extract.ml testextract.ml -cclib -lcamlplus -ccopt -L.

testextract: testextract.out
	./$<

clean:
	ocamlbuild -clean
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$(RM) -r Makefile.coq* *.[oa] *.so *.cm[ixoa] *.cmx* *.opt *~ $(TMP_DIR)
