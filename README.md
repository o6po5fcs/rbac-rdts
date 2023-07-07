# Secure RDTs: Enforcing Access Control Policies for Offline Available JSON Data (Artifact)

## Overview

```text
root/
├─ code/
│  ├─ formalisation/
│  │  ├─ CommonLang.rkt              - Redex implementation of CommonLang
│  │  ├─ LeaderLang.rkt              - Redex implementation of LeaderLang
│  │  ├─ primitive-operations.rkt    - Some axiliary primitive operations
│  │  ├─ ReplicaLang.rkt             - Redex implementation of ReplicaLang
│  ├─ interactivity/
│  │  ├─ CLI.rkt                     - Implementation of a "CLI" tool interact with an SRDT (interactions between ReplicaLang and LeaderLang)
│  ├─ rendering/
│  │  ├─ rendering.rkt
│  ├─ testing/
│  │  ├─ LeaderLang-testcases.rkt    - Some manual testcases for LeaderLang
│  │  ├─ random-testing.rkt          - Randomized testing suite for LeaderLang and ReplicaLang
│  │  ├─ ReplicaLang-testcases.rkt   - Some manual testcases for ReplicaLang
│  │  ├─ test-data.rkt               - Some test data used for manual testing
│  ├─ bugs-randomised-testing.txt    - Report of the bugs in the formalism that were caught via randomised testing
│  ├─ motivating-example.rkt         - The motivating example used in the paper, which can be interacted with.
│  ├─ read-tests.sh                  - Script to quickly execute randomised read tests and log their output to ./logs/reads-X.txt. There are 2 mandatory command-line arguments, namely the number of cores and the number of iterations per core (e.g., `./read-tests.sh 128 7813`)
│  ├─ write-tests.sh                 - Script to quickly execute randomised write tests and log their output to ./logs/writes-X.txt. There are 2 mandatory command-line arguments, namely the number of cores and the number of iterations per core (e.g., `./write-tests.sh 128 7813`)
├─ Artifact.pdf                      - Artifact documentation
├─ code-examples.txt                 - Sample ReplicaLang code that can be used in the CLI
├─ Dockerfile
```
