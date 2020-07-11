COQMAKEFILE ?= Makefile.coq

all: $(COQMAKEFILE) foo.py
	@$(MAKE) -f $<

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ $@
	$(RM) $(COQMAKEFILE) $(COQMAKEFILE).conf

$(COQMAKEFILE): _CoqProject
	@coq_makefile -o $@ -f $<

