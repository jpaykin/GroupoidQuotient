# GroupoidQuotient

Formalizes groupoid quotients using the HoTT library in Coq. This is intended to supplement the paper `A HoTT Quantum Equational Theory`.

## Contents

  - `Groupoid.v` defines groupoids---categories where every morphism is invertible
  - `GroupoidQuotient.v` defines a higher inductive type that encodes groupoid morphisms as paths. The file also provides several induction and recursion principles for using this type.
  
## Correspondence to paper proofs

Proposition 2: `cell_compose` in `GroupoidQuotient.v`.

Proposition 5: `quotient1_1` in `GroupoidQuotient.v`.

Proposition 6: `quotient1_inv` in `GroupoidQuotient.v`.

Lemma 7: `quotient1_rec2` in `GroupoidQuotient.v`.


## Build

This repository can be compiled using the `hoq` tool found at [https://github.com/HoTT/HoTT]. Follow the instructions in that repository to build the tool. If the command `hoqc` is not on your PATH, edit the Makefile with a path to the binary. Then execute `make` to build the files in this repository.

Alternatively, it is possible to set up ProofGeneral to use `hoqtop` as an interactive prover, in which case you can dynamically explore these files. See the HoTT library repository for more information.
