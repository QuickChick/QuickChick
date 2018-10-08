#!/bin/bash 

# timeout in seconds
TIMEOUT=10
for i in `seq 0 20`; do
    for prop in EENI SSNI MSNI; do
        for mode in naive medium smart; do
            echo "Handling : ${prop} ${mode} exp_result_fuzz ${i}" 
            cp Driver.v Tmp.v 
            echo "FuzzChick (testMutantX prop_${prop}_${mode} exp_result_random ${i})." >> Driver.v
            coqc Driver.v -Q . QuickChick.ifcbasic > output/fuzz_${prop}_${mode}_${i}.out
            cp Tmp.v Driver.v
        done
    done
done

for i in `seq 0 20`; do
    for prop in EENI SSNI MSNI; do
        for mode in naive medium smart; do
            echo "Handling : ${prop} ${mode} exp_result_random ${i}" 
            cp Driver.v Tmp.v 
            echo "QuickChick (testMutantX prop_${prop}_${mode} exp_result_random ${i})." >> Driver.v
            coqc Driver.v -Q . QuickChick.ifcbasic > "output/rand_${prop}_${mode}_${i}.out"
            cp Tmp.v Driver.v
        done
    done
done

