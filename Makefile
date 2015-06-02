
.PHONY: plugin install clean

# Here is a hack to make $(eval $(shell work
# (copied from coq_makefile generated stuff):
define donewline


endef

includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

plugin: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq src/quickChickLib.cmx src/quickChickLib.o
	$(MAKE) -f Makefile.coq install
        # Manually copying the remaining files
	cp src/quickChickLib.cmx $(COQLIB)/user-contrib/QuickChick
	cp src/quickChickLib.o $(COQLIB)/user-contrib/QuickChick

tests:
	coqc examples/Tests.v
	cd examples/RedBlack; make clean && make
	cd examples/stlc; make clean && make
	cd examples/ifc-basic; make clean && make && coqc Driver.v

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq

clean:
         # This might not work on macs, but then not my problem
	find . -regex ".*\.vo\|.*\.d\|.*\.glob\|.*\.o\|.*\.cmi\|.*\.cmx\|.*\.cmxs\|.*\.cmo\|.*\.bak\|.*~" -type f -delete
	rm -f Makefile.coq

bc:
	coqwc src/*.v
