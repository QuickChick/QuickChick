#!/bin/sh
set -xe

coqc test_extraction.v > test_extraction.out
diff test_extraction.out test_extraction.ref

coqc test_splitmix.v
