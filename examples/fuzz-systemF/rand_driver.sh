#!/bin/bash
# Usage:  ./rand_driver per_run total 
for run in `seq 0 $2`; do
  export LOW=$(expr $run \* $1)
  export HI=$(expr $run \* $1 + $1 - 1)
  echo $LOW
  echo $HI
  export MODE=$3
  echo './rand_driver_one_run.sh 1 19 $LOW $HI 50000000 500000000 $MODE'
  screen -S run$run -dm bash -c './rand_driver_one_run.sh 1 19 $LOW $HI 50000000 500000000 $MODE'
  sleep 1
done

