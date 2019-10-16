#!/bin/bash
# Usage:  ./rand_driver mut_low mut_high run_low run_high successes discards gen
# Common: ./rand_driver 1 19 0 20 50000000 50000000 naive/smart
for run in `seq $3 $4`; do
  for i in `seq $1 $2`; do
    echo "Handling mutant #$i with generator $7"
    cp lambda.v Tmp.v
    echo "Extract Constant defNumTests => \"$5\"." >> Tmp.v
    echo "Extract Constant defNumDiscards => \"$6\"." >> Tmp.v

    echo "Definition prop_specialized :=" >> Tmp.v
    echo "  let c := List.nth $i all_mutants NoMutant in" >> Tmp.v
    echo "  prop_preservation_$7 c." >> Tmp.v
    echo "" >> Tmp.v
    echo "QuickChick prop_specialized. " >> Tmp.v

    export J=$i
    export FN="output/$7-$5-$J-$run.out"
    echo "coqc -Q . QuickChick.FuzzSTLC Tmp.v &> $FN"
    coqc -Q . QuickChick.FuzzSTLC Tmp.v &> $FN
    sleep 2
  done
done

