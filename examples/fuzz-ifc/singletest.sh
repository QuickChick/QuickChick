#!/bin/bash 

echo "Handling : $1 $2 exp_result_fuzz $3" 
cp Driver.v Tmp.v 
echo "FuzzChick (testMutantX prop_$1_$2 exp_result_fuzz $3)." >> Driver.v
coqc Driver.v -Q . QuickChick.ifcbasic &> output/fuzz_$1_$2_$3.out
cp Tmp.v Driver.v
