#!/bin/sh
set -e
MUTATION=mutation

# Extract and compile the example
coqc ${MUTATION}.v
EXTRACTED=mutation.ml
sed 's/Uint63.of_int//g' -i ${EXTRACTED}
ocamlbuild -pkg zarith -pkg pure-splitmix ${MUTATION}.native

# Look for mutants and test them
PATH=../../scripts:$PATH quickchick ./${MUTATION}.native 4
