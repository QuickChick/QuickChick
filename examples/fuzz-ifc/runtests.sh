#!/bin/bash

for i in `seq 0 19`; do
    for prop in SSNI; do
        for mode in smart; do
            echo "Handling : ${prop} ${mode} exp_result_fuzz ${i}"
            cp Driver.v Tmp.v
            echo -e "\nFuzzChick (testMutantX prop_${prop}_${mode} exp_result_fuzz ${i})." >> Tmp.v
            coqc Tmp.v -Q . QuickChick.ifcbasic &> output/fuzz_${mode}_${i}.out
            sleep 5
        done
    done
done

#for i in `seq 0 19`; do
#    for prop in SSNI; do
#        for mode in arbitrary; do
#            echo "Handling : ${prop} ${mode} exp_result_random ${i}"
#            cp Driver.v Tmp.v
#            echo -e "\nQuickChick (testMutantX prop_${prop}_${mode} exp_result_random ${i})." >> Tmp.v
#            coqc Tmp.v -Q . QuickChick.ifcbasic &> output/rand_${mode}_${i}.out
#            sleep 2
#        done
#    done
#done
