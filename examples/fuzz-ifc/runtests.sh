#!/bin/bash

for i in `seq 0 19`; do
    for prop in SSNI; do
        for mode in arbitrary; do
            echo "Handling : ${prop} ${mode} exp_result_fuzz ${i}"
            cp Driver.v Tmp.v
	    echo -e "\nFuzzChick (testMutantX prop_${prop}_${mode} exp_result_fuzz ${i})." >> Tmp.v
            coqc Tmp.v -Q . QuickChick.ifcbasic &> output/fuzz_seeded_${prop}_${mode}_${i}.out
        done
    done
done

#for i in `seq 0 19`; do
#    for prop in SSNI; do
#        for mode in arbitrary arbmedium smart; do
#            echo "Handling : ${prop} ${mode} exp_result_random ${i}"
#            cp Driver.v Tmp.v
#            echo "QuickChick (testMutantX prop_${prop}_${mode} exp_result_random ${i})." >> Driver.v
#            coqc Driver.v -Q . QuickChick.ifcbasic &> "output/rand_${prop}_${mode}_${i}.out"
#            cp Tmp.v Driver.v
#        done
#    done
#done

