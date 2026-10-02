# Superadditivity of classical communication
This repository provides Lean verification of the following arXiv papers, alongside Python codes for numerical calculations if needed.

| Paper | Available files |
| --- | --- |
| arXiv:2607.15210 | [Lean proofs, installation guide, and Python certificates](./lean_arXiv_2607.15210/README.md) |
| arXiv:2608.25961 | [Numerical reproducibility code](reproduce_numerics.py) |
| arXiv:2609.26743 | [`lean_arXiv:2609.26743/`](./lean_arXiv:2609.26743/README.md) |

For arXiv:2607.15210, the [verification guide](lean_arXiv_2607.15210/README.md)
starts with installation instructions and indexes all 20 requested numbered
results, with exact Lean declarations and every related local proof file.
The channel-limit and existence results use only the stated block-modified
strong-convergence theorem. The remaining spectral, entropy, operator, and
optimization steps are proved in Lean. The dimension-182 result includes the
global minimizer reduction and an exact rational Python certificate for a gap
greater than 0.000477 nats; its conclusion is `k_high(1) <= 182).

```sh
bash lean_arXiv_2607.15210/verify-all.sh
```

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

## Citation

For the Lean verification of arXiv:2609.26743, use:

```bibtex
@misc{wu_lean_2609_26743,
  author       = {Wu, Peixue},
  title        = {{Lean verification for explicit channels with unbounded gains in classical communication using entangled inputs}},
  howpublished = {\href{https://github.com/pxwu24/superadditivity-of-classical-communication/tree/5f4ddefcb814141acdf2a8957beb4f7c7382e86d/lean_arXiv:2609.26743}{Github Repository}}
}
```

Load `\usepackage{hyperref}` in your LaTeX preamble. The bibliography displays
only the clickable label “Github Repository”; the link identifies a fixed
code snapshot without printing its URL or commit hash.
