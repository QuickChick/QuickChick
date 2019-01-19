#!/bin/bash

ocamlopt -afl-instrument C.ml
ocamlopt C.cmx -o foo Fuzz.ml SHM.c
ocamlopt -o main Main.ml SHM.c
