QC=quickChick -color -ocamlbuild '-lib unix'

all: Makefile.coq Foo
	@$(MAKE) -f $<

test:
	time $(QC)

lesstest:
	time $(QC) -N 100

Makefile.coq: _CoqProject
	@coq_makefile -o $@ -f $<
