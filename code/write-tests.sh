#!/bin/bash

if [ ! -d "logs" ]; then
  mkdir logs
fi

# run processes and store pids in array
for ((i=1;i<=$1;i++)); do
    racket -l racket/base -t "./testing/random-testing.rkt" -e "(run-write-tests $2)" 2>&1 > ./logs/writes-${i}.txt &
    pids[${i}]=$!
done

# wait for all pids
for pid in ${pids[*]}; do
    wait $pid
done

# loop through the log files
for ((i=1;i<=$1;i++)); do
  # get the last line of each log file
  last_line=$(tail -n 1 ./logs/writes-$i.txt)
  # check if the last line ends with "OK"
  if [[ $last_line != *"OK" ]]; then
    # output error and exit the loop
    echo "error: ./logs/writes-$i.txt"
    exit 1
  fi
done

# output all good if no error was found
echo "Write tests succeeded"