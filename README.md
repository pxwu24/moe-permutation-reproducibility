# Superadditivity of classical communication
This repository groups numerical code and formal proofs by arXiv paper.

| Paper | Available files |
| --- | --- |
| arXiv:2607.15210 | Lean files not yet included |
| arXiv:2608.25961 | [Numerical reproducibility code](reproduce_numerics.py) |
| arXiv:2609.26743 | [`lean_arXiv:2609.26743/`](./lean_arXiv:2609.26743/README.md) |

The Lean project for arXiv:2609.26743 formalizes the Supplement and the main
theorem of *Explicit channels with unbounded gains in classical communication
using entangled inputs*.

The active Lean 4.33 project combines the adder trace bounds, entropy estimates,
actual channel construction, finite-field Pauli randomization, Holevo bounds,
and parameter and dimension estimates. Its main theorem constructs channels
with one-copy Holevo information below `1/N` and two-copy Holevo information
above `N`, for every real `N ≥ 1`.

```sh
bash lean_arXiv:2609.26743/verify-all.sh
```

See the [verification guide](./lean_arXiv:2609.26743/README.md) for each supplemental result,
its Lean theorem, and the commands to check it. The [coverage map](./lean_arXiv:2609.26743/COVERAGE.md)
explains the hypotheses and representation conventions. The regularized-capacity
corollary uses the regularized Holevo definition; the operational coding theorem
is not re-proved here.
