# Superadditivity of classical communication
This repository groups numerical code and formal proofs by arXiv paper.

| Paper | Available files |
| --- | --- |
| arXiv:2607.15210 | [Lean verification and output-dimension-182 certificate](./lean_arXiv_2607.15210/README.md) |
| arXiv:2608.25961 | [Numerical reproducibility code](reproduce_numerics.py) |
| arXiv:2609.26743 | [`lean_arXiv:2609.26743/`](./lean_arXiv:2609.26743/README.md) |

For arXiv:2607.15210, the new `k182` certificate establishes the upper bound
`k_high(1) <= 182`, with a strict limiting von Neumann entropy gap greater
than `0.000477` nats. It includes reproducible Python interval arithmetic,
the analytic proof, and Lean checks of the scalar and numerical bounds.
The Lean entropy conclusion has an explicit minimizer-shape hypothesis;
that analytic reduction is not yet formalized. See the paper folder for
the exact verification scope.

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
