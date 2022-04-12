#!/bin/sh
set -e
MUTATION=mutation

# Extract and compile the example
coqc ${MUTATION}.v
EXTRACTED=mutation.ml
ocamlfind opt -package zarith,pure-splitmix,coq-simple-io.extraction -linkpkg -o ${MUTATION}.native ${MUTATION}.mli ${MUTATION}.ml

# Look for mutants and test them
PATH=../../scripts:$PATH quickchick ./${MUTATION}.native 4
