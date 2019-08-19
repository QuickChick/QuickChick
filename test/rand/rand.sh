#!/bin/sh
coqc -Q ../../src QuickChick rand.v
ocamlfind ocamlopt -rectypes -package threads,coq.kernel -thread kernel.cmxa rand.mli rand.ml randexe.ml -o randexe
