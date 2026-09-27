# Quantum-channel reproducibility

This repository contains numerical code and formal proofs for two related
quantum-channel projects.

- [`reproduce_numerics.py`](reproduce_numerics.py): numerical reproducibility
  code for *Additivity violations of minimum output entropy via random and
  deterministic permutations*.
- [`lean/`](lean/README.md): Lean verification of the Supplemental Material of
  *Explicit channels with unbounded gains in classical communication using
  entangled inputs*.

The Lean collection covers the Supplement's technical results. The final
main-result proof and its parameter/dimension analysis are outside this
collection. See the [coverage map](lean/COVERAGE.md) for the precise scope,
theorem names, assumptions, and verification records.
