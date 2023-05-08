# Secure RDTs: Enforcing Access Control Policies for JSON Replicated Data Types (Artifact)

## Overview

```
secure-replication/
├─ formalisation/
│  ├─ LeaderLang.rkt              - Redex implementation of LeaderLang
│  ├─ CommonLang.rkt              - Redex implementation of CommonLang
│  ├─ ReplicaLang.rkt             - Redex implementation of ReplicaLang
│  ├─ primitive-operations.rkt    - Some axiliary primitive operations
├─ interactivity/
│  ├─ CLI.rkt                     - Implementation of a "CLI" tool interact with a replica, and to provide interactions between ReplicaLang and LeaderLang
├─ testing/
│  ├─ LeaderLang-testcases.rkt    - Some manual testcases for LeaderLang
│  ├─ ReplicaLang-testcases.rkt   - Some manual testcases for ReplicaLang
│  ├─ random-testing.rkt          - Randomized testing suite for LeaderLang and ReplicaLang
│  ├─ test-data.rkt               - Some test data used for manual testing
├─ motivating-example.rkt         - The motivating example used in the paper, which can be interacted with.
├─ bugs-randomized-testing.txt    - Report of the bugs in the formalism that were caught via randomized testing
├─ read-test-128.sh               - Script to quickly execute ./testing/random-testing.rkt 128 times and log their output to ./logs/reads-X.txt
├─ write-test-128.sh              - Script to quickly execute ./testing/random-testing.rkt 128 times and log their output to ./logs/writes-X.txt
```
