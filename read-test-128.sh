#!/bin/bash


# run processes and store pids in array
for i in {1..128}; do
    ../racket/bin/racket ./testing/random-testing.rkt 2>&1 > ./logs/reads-${i}.txt &
    pids[${i}]=$!
done

# wait for all pids
for pid in ${pids[*]}; do
    wait $pid
done

# loop through the log files
for i in {1..128}
do
  # get the last line of each log file
  last_line=$(tail -n 1 ./logs/reads-$i.txt)
  # check if the last line ends with "OK"
  if [[ $last_line != *"OK" ]]; then
    # output error and exit the loop
    echo "error: ./logs/reads-$i.txt"
    exit 1
  fi
done

# output all good if no error was found
echo "Read tests succeeded"