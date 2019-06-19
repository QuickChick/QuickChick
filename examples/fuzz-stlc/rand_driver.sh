#!/bin/bash

for i in `seq $1 $2`; do
    echo "Handling mutant #$i with generator $3"
    cp lambda.v Tmp.v
    echo "Definition prop_specialized :=" >> Tmp.v
    echo "  let c := List.nth $i all_mutants NoMutant in" >> Tmp.v
    echo "  prop_preservation_$3 c." >> Tmp.v
    echo "" >> Tmp.v
    echo "QuickChick prop_specialized. " >> Tmp.v
    coqc Tmp.v -Q . QuickChick.FuzzSTLC &> output/qc_$3_${i}.out
done
