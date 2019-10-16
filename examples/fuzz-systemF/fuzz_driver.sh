#!/bin/bash
# Usage:  ./fuzz_driver per_run total 
for run in `seq 0 $2`; do
  export LOW=$(expr $run \* $1)
  export HI=$(expr $run \* $1 + $1 - 1)
  echo $LOW
  echo $HI
  echo './fuzz_driver_one_run.sh 1 19 $LOW $HI 10000000 100000000 $MODE'
  screen -S run$run -dm bash -c './fuzz_driver_one_run.sh 1 19 $LOW $HI 10000000 100000000'
  sleep 2
done
