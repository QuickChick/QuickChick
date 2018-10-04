#!/bin/bash 

for i in `seq 0 20`; do
    for prop in EENI SSNI MSNI; do
        for mode in naive medium smart; do
            echo "Handling : ${prop} ${mode} exp_result_random ${i}" 
            cp Driver.v Tmp.v 
            echo "QuickChick (testMutantX prop_${prop}_${mode} exp_result_random ${i})." >> Driver.v
            coqc Driver.v -Q . QuickChick.ifcbasic > "output/prop_${prop}_${mode}_${i}.out"
            cp Tmp.v Driver.v
        done
    done
done

