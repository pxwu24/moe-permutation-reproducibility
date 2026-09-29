# Unified formalization of the Supplement and main theorem

This Lean 4.33 project contains the entropy, adder, filter, randomizer, and
Holevo proofs in one import graph. Start with [`AllProofs.lean`](AllProofs.lean)
or the [paper-to-Lean coverage map](../COVERAGE.md).

| Statement | Principal endpoint |
| --- | --- |
| Lemma 3: single-copy estimate | `SupplementSingle.lemma3` |
| Lemma 4: Bell-input entropy sandwich | `SupplementEntropy.lemma4` |
| Corollary 1: actual tensor-coordinate estimate | `SupplementEntropy.corollary1` |
| Corollary 2: linear and unbounded entropy gap | `SupplementEntropy.corollary2`, `SupplementEntropy.corollary2_unbounded` |
| Proposition 2: uniform measurement estimate | `ActualGridSupport.actual_grid_support_bound` |
| Proposition 3: prescribed filter trace | `AdderTrace.technical_trace_bound` |
| Lemmas 5–6: word and moment estimates | `SupplementAdder.lemma5_word_trace`, `SupplementAdder.lemma6_moment_bound` |
| Main theorem: both strict Holevo bounds | `MainTheorem.main_theorem` |
| Dimensions of the same channels | `MainTheorem.main_dimensions` |
| Parameter table growth rates | `MainParameterGrowth.L_theta`, `q_theta`, `log_Q_theta`, `log_inputDimension_theta`, `C₂_theta`, `log_outputDimension_theta` |
| Unbounded regularized-capacity gap | `MainCapacityCorollary.unbounded_capacity_gap` |

The main theorem has only the premise `1 ≤ N`. Its imported proofs construct
the adder matrices, full Gaussian-grid filter, measurement channel, finite-field
Pauli randomizer, and classical Pauli completion. The required trace, norm,
entropy, and twirling bounds are proved for those objects.

The general Supplement statements retain their stated hypotheses. In
particular, the channel-entry and conjugate-entry hypotheses specify the
channel formulas; they do not assume the desired entropy or marginal bounds.
`MainChannel`, `MainReal`, and `MainConcreteBasic` discharge these conditions
for the actual main-theorem construction.

The randomizer uses Mathlib's `GaloisField 2 t` and the field trace. The proof is
independent of a chosen polynomial representation; it does not implement the
lexicographically first irreducible-polynomial search. Capacity is formalized
by its regularized Holevo formula, without re-proving the operational coding
theorem. These distinctions are explained in [COVERAGE.md](../COVERAGE.md).

## Reproduce

Install Git, Python 3, Bash 4 or newer, and [elan](https://github.com/leanprover/elan).
From this directory, run:

```sh
bash verify.sh
```

| Dependency | Pinned version |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Physlib | `c76e3ccab04eacb69a126ca5c021b0788d513292` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |

The script checks out Physlib, applies the published `upstream.patch`, obtains
standard Mathlib dependency artifacts, and builds the required Physlib modules.
It then compiles every local `.lean` source, including `AllProofs.lean`, and
checks every declaration originating in those modules. The axiom audit follows
dependencies transitively and allows only `propext`, `Classical.choice`, and
`Quot.sound`.

An existing pinned checkout can be selected with:

```sh
PHYSLIB_DIR=/absolute/path/to/physlib bash verify.sh
```

`SKIP_CACHE_DOWNLOAD=1` uses already available dependency artifacts; every local
proof is still rebuilt. `VERIFICATION_DIR` changes the output directory from
its default, `verification/`.

Each run records compiler output, the exhaustive axiom audit, exact source
hashes, build order, dependency versions, and `verification_status.json`.
The success record is written only after the entire build and audit pass.
Use its source manifest to identify exactly which source versions were checked;
a record from the earlier Supplement-only collection does not certify later
main-theorem additions.

Attribution and the dependency patch are documented in
[`NOTICE.md`](NOTICE.md), with the applicable third-party license in
[`LICENSE-APACHE-2.0.txt`](LICENSE-APACHE-2.0.txt).

## Revised final Supplement (2026-09-29)

`MainSharperPostprocessing` proves the revised coefficient
`d_M(s) - 2 log(1+9/M)` with an explicit logarithmic error, both for the
actual Bell-output entropy and for the final channel's two-copy Holevo
information. The main theorem and explicit dimension estimates are unchanged.
The manuscript must retain the explicit Pauli postprocessing construction
and its proof; tensoring the adder tuple alone does not give the stated
vanishing one-copy bound.

## Current verification result

The fresh 2026-09-29 aggregate run passed with exit code 0: **58 local proof
modules** were rebuilt from source and **2,054 originating declarations**
passed the exhaustive transitive axiom audit. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The successful source manifest
matches the current proof files, including `MainSharperPostprocessing.lean`.

Current record: [`verification-2026-09-29/verification_status.json`](verification-2026-09-29/verification_status.json).
