# Lean verification of the paper

This collection accompanies *Explicit channels with unbounded gains in
classical communication using entangled inputs*. The active project covers
Lemmas 3–6, Corollaries 1–2, Propositions 2–3, and the main theorem, including
the prescribed parameters and dimension estimates.

## Projects

| Directory | Toolchain | Role |
| --- | --- | --- |
| [`entropy`](entropy/) | Lean 4.33.0; pinned Physlib and mathlib | Unified proof project, including all adder proofs and the main theorem |
| [`adder-trace`](adder-trace/) | Lean 4.24.0; pinned mathlib | Preserved original adder proof project, optional to rebuild |

[`entropy/AllProofs.lean`](entropy/AllProofs.lean) imports the paper-facing
results. `MainTheorem.main_theorem` proves both strict Holevo inequalities for
an actual, fully specified CPTP map. `MainTheorem.main_dimensions` bounds the
dimensions of that same map. `MainParameterGrowth` supplies the `IsTheta`
statements underlying the parameter table.

The Lean 4.24 project is retained for provenance. The active proof imports the
ported adder modules inside the Lean 4.33 project; no compiled proof is imported
across toolchains.

## Reproduce

Install Git, Python 3, Bash, and the
[elan Lean toolchain manager](https://github.com/leanprover/elan).
From the repository root run:

```sh
bash lean/verify-all.sh
```

To additionally check the unchanged original Lean 4.24 adder project:

```sh
VERIFY_LEGACY_ADDER=1 bash lean/verify-all.sh
```

The verifier checks pinned dependency revisions, rebuilds every local Lean
source in dependency order, and audits every originating declaration's
transitive axiom dependencies. It rejects `sorryAx` and additional axioms;
only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

See [COVERAGE.md](COVERAGE.md) for the correspondence with the paper and the
precise scope of the finite-field representation and capacity statements.
Dependency notices are preserved in [`entropy/NOTICE.md`](entropy/NOTICE.md).
