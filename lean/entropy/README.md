# Entropy and filter proofs

This project formalizes the entropy, tensor, and filter estimates in the
Supplement. The [coverage map](../COVERAGE.md) identifies the corresponding
statements and their assumptions.

| Statement | Lean endpoint |
| --- | --- |
| Lemma 3, including the pointwise Hilbert–Schmidt estimate | `SupplementSingle.lemma3` |
| Lemma 4, including the Bell-input sandwich | `SupplementEntropy.lemma4` |
| Corollary 1 for the actual tensor tuple | `SupplementEntropy.corollary1` |
| Corollary 2 and its unbounded-gap consequence | `SupplementEntropy.corollary2`, `SupplementEntropy.corollary2_unbounded` |
| Proposition 3, the Gaussian-grid filter support estimate | `ActualGridSupport.actual_grid_support_bound` |

The channel parameters `hΦ` and `hconj` specify the matrix-entry formula and
the complex-conjugate channel. The tensor marginal identities are derived in
the proof of Corollary 1, for arbitrary complex unitary factors. The suppressor
and trace bounds remain the hypotheses stated in the corresponding Supplement
results.

The source modules are organized into four groups:

- `BellAlgebra`, `FilterTrace`, `Joint*`, `Single*`, and `TensorBridge` prove the
  single-channel and two-channel estimates.
- `ActualTensor*`, `ActualCoordinateMarginal`, and `TensorMarginalEntropy`
  construct tensor labels and prove the coordinate marginal formulas.
- `Grid*`, `GaussianSign*`, `SignFilterLower`, `FiniteFilterSupport`, and
  `ActualGrid*` prove the concrete filter and support estimates.
- `Gap*`, `TensorAmplification`, `SymbolicAmplification`, and `TensorCalibration`
  supply the scalar estimates used by the two corollaries.

`SupplementSingle.lean` and `SupplementEntropy.lean` provide the paper-facing
statements. The final main-result construction is outside this project.

## Reproduce

Install Git, Python 3, Bash 4 or newer, and [elan](https://github.com/leanprover/elan).
From this directory, run:

```sh
bash verify.sh
```

The dependencies are pinned to:

| Dependency | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Physlib | `c76e3ccab04eacb69a126ca5c021b0788d513292` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |

The script checks out Physlib, applies the published `upstream.patch`, obtains
the standard Mathlib dependency cache, and builds the required Physlib modules.
It then compiles **every local proof source** in dependency order and audits
every declaration originating in those modules. The audit follows dependencies
transitively and fails on `sorryAx` or any axiom other than `propext`,
`Classical.choice`, and `Quot.sound`.

An existing checkout at the pinned Physlib revision can be selected with:

```sh
PHYSLIB_DIR=/absolute/path/to/physlib bash verify.sh
```

`SKIP_CACHE_DOWNLOAD=1` uses already available standard dependency artifacts.
All local proofs are still recompiled. `VERIFICATION_DIR` selects a different
output directory; the default is `verification/`.

Each run writes a compiler log, an exhaustive axiom-audit log, exact source
hashes, the build order, dependency versions, and `verification_status.json`.
The JSON success record is created only after compilation and the aggregate
audit both pass.

Dependency attribution and the compatibility-patch description are in
[`NOTICE.md`](NOTICE.md); the applicable third-party license text is in
[`LICENSE-APACHE-2.0.txt`](LICENSE-APACHE-2.0.txt).
