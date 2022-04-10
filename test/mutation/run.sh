#!/bin/sh
set -e
MUTATION=mutation

# Extract and compile the example
coqc ${MUTATION}.v
EXTRACTED=mutation.ml
ocamlbuild -pkg zarith,pure-splitmix,coq-core.kernel -cflags -rectypes ${MUTATION}.native

# Look for mutants and test them
PATH=../../scripts:$PATH quickchick ./${MUTATION}.native 4
