all: Makefile.coq Foo extract.cmxs
	@$(MAKE) -f $<

test:
	time quickChick -color -ocamlbuild '-lib unix'

Makefile.coq: _CoqProject
	@coq_makefile -o $@ -f $<

%.cmxs: %.ml
	ocamlopt -shared -o $@
