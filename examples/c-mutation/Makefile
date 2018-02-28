all: Makefile.coq Foo extract.cmxs
	@$(MAKE) -f $<

test:
	quickChick -ocamlbuild '-lib unix'

Makefile.coq: _CoqProject
	@coq_makefile -o $@ -f $<

%.cmxs: %.ml
	@ocamlbuild $@
	@mv _build/$@ .
	@ocamlbuild -clean
