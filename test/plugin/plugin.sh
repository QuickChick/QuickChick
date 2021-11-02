#!/bin/sh
set -e

cppo -V COQ:`coqc -print-version | awk '{print $1}'` -n -o plugin.v plugin.v.cppo

# Just test this compiles
coqc -Q ../../src QuickChick plugin.v
