#!/bin/bash

for i in `seq $1 $2`; do
    echo "Handling mutant #: $i"
    cp lambda.v Tmp.v
    echo "Definition prop_specialized (e : Term) : option bool :=" >> Tmp.v
    echo "  let c := List.nth $i all_mutants NoMutant in" >> Tmp.v
    echo "  preservation' c e." >> Tmp.v
    echo "" >> Tmp.v
    echo "Definition fuzzLoop :=" >> Tmp.v
    echo "  fun _ : unit =>" >> Tmp.v
    echo "    fuzzLoop arbitrary fuzz show prop_specialized." >> Tmp.v
    echo "" >> Tmp.v
    echo "FuzzQC prop_specialized (fuzzLoop tt). " >> Tmp.v
    coqc Tmp.v -Q . QuickChick.FuzzSTLC &> output/qc_fuzz_${i}.out
done
