# Unified Lean proof project

This project contains the entropy, measurement, adder, moment, parameter,
postprocessing, and Holevo proofs for the Supplemental Material.
[`AllProofs.lean`](AllProofs.lean) is the entry point.

Use the [verification guide](../README.md) to find the Lean theorem for each
mathematical result and inspect its assumptions. The
[coverage guide](../COVERAGE.md) explains the formalization scope.

## Build and audit

Install Git, Python 3, Bash 4 or newer, and
[elan](https://github.com/leanprover/elan). From this directory, run:

```sh
bash verify.sh
```

Equivalently, from the repository root, run `bash lean/verify-all.sh`.

| Dependency | Pinned version |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Physlib | `c76e3ccab04eacb69a126ca5c021b0788d513292` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |

The verifier obtains Physlib, applies [`upstream.patch`](upstream.patch),
restores standard Mathlib dependency artifacts, and builds the required
Physlib modules. It copies the local proof sources into the pinned Physlib
checkout, recompiles them in dependency order, and audits every originating
declaration. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
A proof placeholder or additional axiom causes the audit to fail.

This directory is not a standalone Lake project. Run individual `lake env lean`
commands inside the prepared Physlib checkout, as shown in the
[verification guide](../README.md).

## Optional settings

Use an existing checkout at the required Physlib commit:

```sh
PHYSLIB_DIR=/absolute/path/to/physlib bash verify.sh
```

Use dependency artifacts already available locally:

```sh
SKIP_CACHE_DOWNLOAD=1 bash verify.sh
```

Write the verification output to another directory:

```sh
VERIFICATION_DIR=/absolute/path/to/results bash verify.sh
```

These settings do not skip rebuilding local proofs or auditing their axioms.

## Verification records

The supplied [aggregate record](verification/verification_status.json) reports
success for **58 modules and 2,054 declarations**, with exit code 0 and only
the three standard axioms above. It includes the exact source manifest.

Each run writes compiler output, the exhaustive axiom audit, dependency
versions, source hashes, and the aggregate result to `verification/` unless
`VERIFICATION_DIR` is set. The success record is written only after the
complete build and audit pass.

Dependency attribution and patch details are in [`NOTICE.md`](NOTICE.md),
with the applicable license in [`LICENSE-APACHE-2.0.txt`](LICENSE-APACHE-2.0.txt).
