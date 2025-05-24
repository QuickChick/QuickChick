#!/bin/bash
perl -i -0pe 's/\)\n    fuzz_fuel\n\n\(\*\* val fuzzLoopWith /\n\n\(\*\* val fuzzLoopWith /' $1
