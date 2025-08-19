# CS 171 - Formal Verification of Pohlig–Hellman (Coq)

This repository contains a machine-checked Coq development of the Pohlig–Hellman algorithm for solving discrete logarithms. It formalizes finite cyclic groups, reduces discrete logs to prime-power cases, and reconstructs solutions via the Chinese Remainder Theorem.

This project was made in fulfillment of requirements for CS 171 Formal Verification and Logic elective class in UP Diliman.

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

## References

- Pohlig, S. C., & Hellman, M. E. (1978). *An improved algorithm for computing logarithms over GF(p) and its cryptographic significance*. IEEE Transactions on Information Theory, 24(1), 106–110.  

- Menezes, A. J., van Oorschot, P. C., & Vanstone, S. A. (1996). *Handbook of Applied Cryptography*. CRC Press.  

- Gallian, J. A. (2017). *Contemporary Abstract Algebra* (9th ed.). Cengage Learning.  

- Coq Development Team. (2023). *The Coq Proof Assistant Reference Manual*. INRIA.  
  Available at: [https://coq.inria.fr/distrib/current/refman/](https://coq.inria.fr/distrib/current/refman/)  

- Lidl, R., & Niederreiter, H. (1997). *Finite Fields*. Cambridge University Press.  

- Ireland, K., & Rosen, M. (1990). *A Classical Introduction to Modern Number Theory*. Springer.  


## License
MIT 
