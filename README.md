# CS171 — Formal Verification of Pohlig–Hellman (Coq)

This repository contains a machine-checked Coq development of the Pohlig–Hellman algorithm for solving discrete logarithms. It formalizes finite cyclic groups, reduces discrete logs to prime-power cases, and reconstructs solutions via the Chinese Remainder Theorem.

## Repository layout
- `coq/` — Coq `.v` source files  
- `doc/` — project report and slides (PDFs)  
- `scripts/` — optional helper scripts / Makefile  
- `README.md` — this file  
- `LICENSE` — project license  

## Requirements
- [Coq](https://coq.inria.fr/) (see `doc/` for the tested version)  
- Optional: `make`, `coq_makefile`, CoqIDE, or VSCode + Coq extension  

## Quick start
```bash
# from repo root

# (optional) generate Makefile if not included
coq_makefile -f _CoqProject -o Makefile coq/*.v

# build/check all Coq files
make

# check a single file
coqc coq/pohlig.v

# interactive development
coqide coq/pohlig.v
# or open with VSCode + Coq extension
```

## Verified components

- Abstract `FiniteCyclicGroup` interface with supporting lemmas
- Verified discrete_log function:
  - reduces discrete logs to prime-power cases
  - uses CRT to reconstruct the global solution
- correctness proven under explicit assumptions
- Some number-theoretic facts (e.g., CRT, factorization) are axiomatized — details in doc/

## Authors
- [Jeremiah Daniel Regalario](https://github.com/jeremiahdanielregalario)
- Marc Dela Paz
- Meluisa Montealto
- Nicole Santos

## License
MIT 
