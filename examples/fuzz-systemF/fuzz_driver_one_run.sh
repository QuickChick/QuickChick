#!/bin/bash
# Usage:  ./fuzz_driver mut_low mut_high run_low run_high successes discards 
# Common: ./fuzz_driver 1 19 0 20 10000000 10000000
for run in `seq $3 $4`; do
  for i in `seq $1 $2`; do
    echo "Fuzzing mutant #: $i"
    cp lambda.v Tmp.v
    echo "Extract Constant defNumTests => \"$5\"." >> Tmp.v
    echo "Extract Constant defNumDiscards => \"$6\"." >> Tmp.v

    echo "Definition prop_specialized (e : Term) : option bool :=" >> Tmp.v
    echo "  let c := List.nth $i all_mutants NoMutant in" >> Tmp.v
    echo "  preservation' c e." >> Tmp.v
    echo "" >> Tmp.v
    echo "Definition fuzzLoop :=" >> Tmp.v
    echo "  fun _ : unit =>" >> Tmp.v
    echo "    fuzzLoop arbitrary fuzz show prop_specialized." >> Tmp.v
    echo "" >> Tmp.v
    echo "FuzzQC prop_specialized (fuzzLoop tt). " >> Tmp.v

    coqc Tmp.v -Q . QuickChick.FuzzSTLC &> output/fuzz-$5-$i-$run.out
 
    sleep 1
  done
done
