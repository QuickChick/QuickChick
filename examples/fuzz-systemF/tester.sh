for i in `seq $1 $2`; do
  echo "Testing Mutant $i.."
  cp Bench.v Tmp.v
  echo "FuzzChick (testMutantX_ fSSNI_medium $i)." >> Tmp.v 
  export J=$i
  echo "screen -S mut$i -dm bash -c 'coqc -R . IFC Tmp.v &> output/output_fuzz_med_2h_$J.out'"
  screen -S mut$i -dm bash -c 'coqc -R . IFC Tmp.v &> output/output_fuzz_med_2h_$J.out'
  sleep 2
done

