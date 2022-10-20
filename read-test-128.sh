#!/bin/bash


# run processes and store pids in array
for i in {1..128}; do
    ../racket/bin/racket random-testing.rkt 2>&1 > ./logs/reads-${i}.txt &
    pids[${i}]=$!
done

# wait for all pids
for pid in ${pids[*]}; do
    wait $pid
done