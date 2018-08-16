#!/bin/sh
set -e
MUTATION=mutation

# Extract and compile the example
coqc -Q ../../src QuickChick ${MUTATION}.v
ocamlbuild -pkg zarith ${MUTATION}.native

# Look for mutants and test them
PATH=../../scripts:$PATH quickchick ./${MUTATION}.native 4
