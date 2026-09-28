# Quantum-channel reproducibility

This repository contains numerical code and formal proofs for two related
quantum-channel projects.

- [`reproduce_numerics.py`](reproduce_numerics.py): numerical reproducibility
  code for *Additivity violations of minimum output entropy via random and
  deterministic permutations*.
- [`lean/`](lean/README.md): Lean formalization of the Supplement and the main
  theorem of *Explicit channels with unbounded gains in classical communication
  using entangled inputs*.

The active Lean 4.33 project combines the adder trace bounds, entropy estimates,
actual channel construction, finite-field Pauli randomization, Holevo bounds,
and parameter and dimension estimates. Its main theorem constructs channels
with one-copy Holevo information below `1/N` and two-copy Holevo information
above `N`, for every real `N ≥ 1`.

```sh
bash lean/verify-all.sh
```

See the [coverage map](lean/COVERAGE.md) for the exact statements, theorem names,
representation conventions, and verification records. The regularized-capacity
corollary uses the regularized Holevo definition; the operational coding theorem
is not re-proved here.
