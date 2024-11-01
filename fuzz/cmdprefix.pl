#!/bin/bash
perl -i -0pe 's/let rec fuzzLoopAux fuzz_fuel st favored discards favored_queue discard_queue randoms saved gen0 fuzz0 print prop =\n  \(fun fO fS n -> if n=0 then fO \(\) else fS \(n-1\)\)\n    \(fun _ -> giveUp st\)\n    \(fun fuzz_fuel\047 ->/let rec fuzzLoopAux fuzz_fuel st favored discards favored_queue discard_queue randoms saved gen0 fuzz0 print prop =\n  if fuzz_fuel = 0 then giveUp st else let fuzz_fuel\047 = fuzz_fuel - 1 in/' $1


