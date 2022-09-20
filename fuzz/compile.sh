#!/bin/bash

ocamlopt -afl-instrument C.ml
ocamlopt -ccopt -Wno-error=implicit-function-declaration C.cmx -o foo Fuzz.ml SHM.c
ocamlopt -ccopt -Wno-error=implicit-function-declaration -o main Main.ml SHM.c
