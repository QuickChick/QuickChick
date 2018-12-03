#!/bin/bash 

echo "Handling : $1 $2 exp_result_fuzz $3" 
cp Driver.v Tmp.v 
echo -e "\nQuickChick (testMutantX prop_$1_$2 exp_result_random $3)." >> Tmp.v
coqc Tmp.v -Q . QuickChick.ifcbasic &> output/rand_$1_$2_$3.out
