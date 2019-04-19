#!/bin/bash

for i in `seq 0 19`; do
    for prop in SSNI; do
        for mode in arbitrary; do
            echo "Handling : ${prop} ${mode} exp_result_fuzz ${i}"
            cp Driver.v Tmp.v
            echo "Definition SSNI_p (v : @Variation State) : option bool :=" >> Tmp.v
            echo "  match nth (mutate_table default_table) $i with" >> Tmp.v
            echo "  | Some t => SSNI t v exp_result_fuzzqc" >> Tmp.v
            echo "  | _ => None" >> Tmp.v
            echo "  end." >> Tmp.v
            echo "" >> Tmp.v
            echo "Definition fuzzLoop :=" >> Tmp.v
            echo "  fun _ : unit =>" >> Tmp.v
            echo "    fuzzLoop (resize 3 gen_variation_arb) fuzz (fun _ => es) SSNI_p." >> Tmp.v
            echo "" >> Tmp.v
            echo "FuzzQC SSNI_p (fuzzLoop tt). " >> Tmp.v
            coqc Tmp.v -Q . QuickChick.ifcbasic &> output/qc_fuzz_${prop}_${mode}_${i}.out
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

