MODULES_QC=Show Gen Arbitrary State Property Test QuickCheck MutateCheck
MODULES_EXTRACT=Extraction Tests
QC_VS      := $(MODULES_QC:%=src/%.v)
EXTRACT_VS := $(MODULES_EXTRACT:%=%.v)
EXTRACT_SH=extract.sh
EXTRACTED=Extracted
SRC := $(QC_VS) $(EXTRACT_VS)
INCLUDE := -I src 
GHC_FLAGS := -rtsopts #-O2 
GHC_OPTS := +RTS -RTS 

all: compile extract haskell 

compile: Makefile.coq
	echo $(SRC)
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(SRC)
	coq_makefile $(SRC) \
		COQC = "coqc " $(INCLUDE) \
		COQDEP = "coqdep " $(INCLUDE) \
		-o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
	rm -f $(EXTRACTED)*

extract: Makefile.coq $(EXTRACT_SH)
	./$(EXTRACT_SH) 

haskell:
	ghc $(GHC_FLAGS) $(EXTRACTED).hs -main-is $(EXTRACTED)
	./$(EXTRACTED) $(GHC_OPTS)
