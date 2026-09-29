# Lean verification for arXiv:2609.26743

This directory formalizes the mathematical results in the Supplemental
Material of *Explicit channels with unbounded gains in classical communication
using entangled inputs*. The unified project is [`entropy/`](entropy/), and
[`AllProofs.lean`](entropy/AllProofs.lean) imports its paper-facing results.

## Verify all results

Install Git, Python 3, Bash 4 or newer, and
[elan](https://github.com/leanprover/elan), with `lake` available on your PATH.
From the repository root, run:

```sh
bash lean_arXiv:2609.26743/verify-all.sh
```

Use Linux, macOS, or a WSL Linux filesystem: the folder name contains a literal
colon, which native Windows filenames do not support. Build files are placed
in `build/arxiv-2609.26743/` at the repository root, since Lean also uses colons
to separate import-search paths.

The script obtains the pinned dependencies, rebuilds every local proof module,
and audits the transitive axiom dependencies of every declaration. A successful
run exits with code `0` and prints `Aggregate audit passed` followed by
`Verification completed`.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. A dependency
on `sorryAx` or an additional axiom makes verification fail.

## Find the proof of a result

Every result in this table is checked by the command above. The source links
open the relevant Lean file; the declaration names identify the exact statements.

| Supplemental result | Lean source | Declaration |
| --- | --- | --- |
| Lemma 3: single-copy entropy estimate | [SupplementSingle.lean](entropy/SupplementSingle.lean) | `SupplementSingle.lemma3` |
| Single-copy Hilbert–Schmidt estimate | [SupplementSingle.lean](entropy/SupplementSingle.lean) | `SupplementSingle.single_copy_hilbertSchmidt_bound` |
| Lemma 4: two-copy Bell-input entropy estimate | [SupplementEntropy.lean](entropy/SupplementEntropy.lean) | `SupplementEntropy.lemma4` |
| Corollary 1: tensor-coordinate entropy estimate | [SupplementEntropy.lean](entropy/SupplementEntropy.lean) | `SupplementEntropy.corollary1` |
| Corollary 2: entropy-gap lower bound and unbounded violation | [SupplementEntropy.lean](entropy/SupplementEntropy.lean) | `SupplementEntropy.corollary2`, `SupplementEntropy.corollary2_unbounded` |
| Proposition 2: uniform measurement estimate | [ActualGridSupport.lean](entropy/ActualGridSupport.lean) | `ActualGridSupport.actual_grid_support_bound` |
| Proposition 3: filter trace estimate | [AdderTrace.lean](entropy/AdderTrace.lean) | `AdderTrace.technical_trace_bound` |
| Lemma 5: word trace estimate | [SupplementAdder.lean](entropy/SupplementAdder.lean) | `SupplementAdder.lemma5_word_trace` |
| Lemma 6: matrix moment estimate | [SupplementAdder.lean](entropy/SupplementAdder.lean) | `SupplementAdder.lemma6_moment_bound` |
| Parameter choice and filter trace error | [MainFilterParameters.lean](entropy/MainFilterParameters.lean) | `MainFilterParameters.prescribedFilter_small` |
| Entropy estimates after Pauli postprocessing | [MainConcreteSmoothed.lean](entropy/MainConcreteSmoothed.lean) | `MainConcreteSmoothed.single_copy`, `MainConcreteSmoothed.two_copy` |
| Sharp Bell-output and two-copy Holevo estimates | [MainSharperPostprocessing.lean](entropy/MainSharperPostprocessing.lean) | `MainSharperPostprocessing.two_copy_sharp`, `MainSharperPostprocessing.holevo_two_copy_sharp` |
| Main theorem: both strict Holevo inequalities | [MainTheorem.lean](entropy/MainTheorem.lean) | `MainTheorem.main_theorem` |
| Input and output dimensions | [MainTheorem.lean](entropy/MainTheorem.lean) | `MainTheorem.main_dimensions` |
| Parameter-table growth rates | [MainParameterGrowth.lean](entropy/MainParameterGrowth.lean) | `MainParameterGrowth.L_theta`, `MainParameterGrowth.q_theta`, `MainParameterGrowth.log_inputDimension_theta`, `MainParameterGrowth.log_outputDimension_theta` |
| Regularized-capacity gap | [MainCapacityCorollary.lean](entropy/MainCapacityCorollary.lean) | `MainCapacityCorollary.unbounded_capacity_gap` |

The [coverage guide](COVERAGE.md) explains the hypotheses and construction
behind these statements, including the remaining parameter-table entries.

## Inspect an individual theorem

First run the complete verifier. It copies the proof sources into the pinned
Physlib project, where Lean can resolve their imports. With the default build
location, run the following from the repository root:

```sh
(
cd build/arxiv-2609.26743/physlib
cat > InspectSupplement.lean <<'LEAN'
import AllProofs

#check SupplementEntropy.lemma4
#print axioms SupplementEntropy.lemma4
LEAN
lake env lean InspectSupplement.lean
)
```

Replace `SupplementEntropy.lemma4` with any declaration in the table.
`#check` displays its hypotheses and conclusion; `#print axioms` displays its
transitive axiom dependencies. Use `#print` instead of `#check` to display
the proof term as well.

To recheck a source module after the full build, run from the repository root:

```sh
(
cd build/arxiv-2609.26743/physlib
lake env lean SupplementEntropy.lean
)
```

These commands inspect the source copies prepared by the full verifier.
After editing files in `lean_arXiv:2609.26743/entropy/`, rerun `bash lean_arXiv:2609.26743/verify-all.sh` from
the repository root to copy the changes, rebuild dependencies, and repeat the
complete axiom audit. If you used `PHYSLIB_DIR`, use that directory in place
of `build/arxiv-2609.26743/physlib`.

## Read the verification records

The supplied successful record covers **58 modules and 2,054 declarations**.
Its source hashes match the proof files in this repository.

| Record | Purpose |
| --- | --- |
| [verification_status.json](entropy/verification/verification_status.json) | Aggregate outcome, dependency versions, counts, and source hashes |
| [verification.log](entropy/verification/verification.log) | Compiler output and audit output |
| [axiom_audit.log](entropy/verification/axiom_audit.log) | Transitive axiom dependencies of each declaration |
| [source_manifest.json](entropy/verification/generated/source_manifest.json) | Exact proof-source hashes and import graph |
| [exit_code.txt](entropy/verification/exit_code.txt) | Process exit code; `0` denotes success |

A new run writes these records only for its own source snapshot. The aggregate
success record is produced after both compilation and the axiom audit pass.

From the repository root, run the numerical parameter cross-check separately:

```sh
python3 lean_arXiv:2609.26743/scripts/check_parameters.py
```

This uses high-precision Decimal arithmetic and is not a Lean certificate.
The saved output is [parameters.json](numerics/parameters.json).

Dependency setup and optional build settings are described in
[`entropy/README.md`](entropy/README.md). The independent
[`adder-trace/`](adder-trace/) project can additionally be checked with
`VERIFY_LEGACY_ADDER=1 bash lean_arXiv:2609.26743/verify-all.sh`.
