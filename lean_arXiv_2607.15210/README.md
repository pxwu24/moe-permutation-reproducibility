# Lean verification for arXiv:2607.15210

Proof sources and numerical certificates for *Counterexamples to additivity of
minimum output p-Rényi entropy of quantum channels for all p ≥ 0*, by Debbie
Leung, Benjamin Lovitz, Ion Nechita, and Peixue Wu. Numbering follows the
attached final draft, identified by its SHA-256 in [RESULTS.json](RESULTS.json).

## Install and verify

Install Git, Bash, and Python 3.11 or newer, including `venv`. The commands
below use Bash; on Windows, run them in WSL. Install Lean's toolchain manager
[elan](https://github.com/leanprover/elan#installation):

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Follow the installer's instructions to add `elan` and `lake` to your `PATH`,
then open a new terminal. This project's `lean-toolchain` automatically selects
Lean **4.19.0**; you do not need to select that version manually.

For a fresh checkout, run:

```sh
git clone https://github.com/pxwu24/superadditivity-of-classical-communication.git
cd superadditivity-of-classical-communication
bash lean_arXiv_2607.15210/verify-all.sh
```

The script obtains the pinned Mathlib dependencies, creates a Python virtual
environment, rebuilds every current Lean source, audits all project declarations,
and runs the Python checks. After setup, rerun without downloading dependencies:

```sh
bash lean_arXiv_2607.15210/verify-all.sh --no-setup
```

Only Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound` are
allowed in the checked source proofs. A dependence on `sorryAx` or any added
logical axiom fails the audit. An explicit theorem hypothesis is still a
hypothesis: an axiom-free conditional theorem does not prove its premise.

All **20 numbered results** listed below are verified. Random-limit and
channel-existence theorems use only the permitted block-modified
strong-convergence input, described below. The default verifier also checks
that no indexed paper result is marked unfinished.

## Find a result and all its Lean files

Each numbered link contains exact declaration names, entry files,
**every transitive local Lean dependency**, and assumptions.
“Spectral” means a theorem about the explicit eigenvalue body or list; its
identification with a channel output is a separate operator statement.

<!-- RESULT_TABLE_START -->
| Paper result | Checked result | Status |
| --- | --- | --- |
| [Lemma II.2](results/II_2.md) | Full local support of a Haar-random subspace | Complete |
| [Lemma II.3](results/II_3.md) | Random compression formula | Complete under the permitted convergence theorem |
| [Lemma A.1](results/A_1.md) | Bernoulli free-convolution spectral edge | Complete |
| [Theorem III.1](results/III_1.md) | Hausdorff limit of output state spaces | Complete under the permitted convergence theorem |
| [Corollary III.2](results/III_2.md) | One-copy entropy limit and asymptotics | Complete under the permitted convergence theorem |
| [Lemma III.3](results/III_3.md) | Support-function formula for trace-norm Hausdorff distance | Complete |
| [Lemma III.4](results/III_4.md) | Channel support and generalized-eigenvalue threshold | Complete |
| [Theorem IV.1](results/IV_1.md) | Limit of the Bell output | Complete under the permitted convergence theorem |
| [Corollary IV.2](results/IV_2.md) | Product-channel bound and Bell entropy expansion | Complete under the permitted convergence theorem |
| [Lemma A.2](results/A_2.md) | Second logarithmic variation | Complete |
| [Proposition A.3](results/A_3.md) | Second moments after local normalization | Complete under the permitted convergence theorem |
| [Proposition A.4](results/A_4.md) | Asymptotic second Choi moment | Complete under the permitted convergence theorem |
| [Theorem V.1](results/V_1.md) | Single-output and Bell-output asymptotics after antisymmetric postprocessing | Complete under the permitted convergence theorem |
| [Proposition V.2](results/V_2.md) | Eigenvalue shuffling | Complete |
| [Proposition B.1](results/B_1.md) | Entropy of the one-channel output body after antisymmetric postprocessing | Complete |
| [Proposition B.2](results/B_2.md) | Entropy of the limiting Bell output after antisymmetric postprocessing | Complete |
| [Theorem I.1](results/I_1.md) | Nonadditivity for every positive Renyi order | Complete under the permitted convergence theorem |
| [Proposition VI.1](results/VI_1.md) | Certified output dimension 182 | Complete |
| [Lemma C.1](results/C_1.md) | Reduction of the entropy minimum | Complete |
| [Lemma C.2](results/C_2.md) | Scalar certificate for the largest eigenvalue | Complete |
<!-- RESULT_TABLE_END -->

The spectral entropy estimates include p = 1. The main channel theorem has
quantifiers **for every p > 0, there exist sufficiently large dimensions**.
It does not assert one finite channel pair that works simultaneously for all p.

## Mathematical input and conventions

The sole external theorem is the **block-modified strong-convergence theorem**.
Its exact interface is [FullBlockModifiedStrongInput](RevisionFullBlockInput.lean):
operator-norm convergence and weak empirical spectral convergence to the same
Bernoulli free-sum law. Free convolution is represented analytically by its
standard inverse-Cauchy/additive-R-transform germ. The interface contains no
spectral-edge, log-potential, normalized-moment, entropy, or nonadditivity formula.

[RevisionCanonicalEnsemble.lean](RevisionCanonicalEnsemble.lean) constructs the
independent Haar sequence and proves its rank-density limit.
`ProjectionChannels.Canonical.CanonicalStrongInput` applies the one permitted
theorem to that concrete ensemble for the channel-existence result. An abstract
C*-algebraic construction of free additive convolution is not a separate claim
of this development.

The numbered guides follow the supplied draft. In Lemma II.3, write
“output-first Choi matrix” for `C_phi = I tensor A`; the preliminaries'
input-first convention gives `J_phi = A tensor I`. Lemma III.3 needs nonempty
sets. The abstract should say **for every p > 0 there exist channels**, with
dimensions allowed to depend on p. These corrections are recorded in
[RESULTS.json](RESULTS.json).

## Inspect an individual theorem

After running the verifier, enter the paper directory and ask Lean to print a
statement and its transitive axioms:

```sh
cd lean_arXiv_2607.15210
cat > InspectResult.lean <<'LEAN'
import AllProofs

#check HaarProjection.haar_projection_partialTrace_rank_fin
#print axioms HaarProjection.haar_projection_partialTrace_rank_fin
#check ProjectionChannels.ScalarCertificate.lemma_C2
#print axioms ProjectionChannels.ScalarCertificate.lemma_C2
LEAN
lake env lean InspectResult.lean
rm InspectResult.lean
```

Replace the names with any declaration from a numbered result guide.
[AllProofs.lean](AllProofs.lean) imports the proof sources;
[ResultChecks.lean](ResultChecks.lean) checks every indexed declaration name.
[AggregateAudit.lean](AggregateAudit.lean) is generated from the complete source
list, so new modules cannot silently escape the axiom audit.

To recheck one source after its dependencies have been built:

```sh
lake env lean RevisionScalarCertificate.lean
```

After changing a proof, rerun the complete verifier to rebuild dependent modules
and renew the source hashes. Mathlib is pinned to
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Read the verification records

| Record | Purpose |
| --- | --- |
| [verification_status.json](verification/verification_status.json) | Compiler/audit outcome, versions, hashes, counts |
| [source_manifest.json](verification/source_manifest.json) | Every compiled source and its imports |
| [axiom_audit.log](verification/axiom_audit.log) | All audited declarations and combined transitive axioms |
| [result_sources.json](verification/result_sources.json) | Numbered theorem index with complete local import closures |
| [paper_coverage.json](verification/paper_coverage.json) | Separate full-paper completion status |
| [python_verification.json](verification/python_verification.json) | Numerical check outcomes |
| [exit_code.txt](verification/exit_code.txt) | Last verifier exit code |

The supplied [BernoulliEdge.lean](SuppliedBernoulliEdge.lean) has been compiled
after targeted import and simplifier repairs. Its `hedge` parameter is an
explicit spectral-edge assumption, so that supplied file alone does not close
Lemma A.1. Its provenance is recorded in [supplied_lean.json](verification/supplied_lean.json).

Earlier audit reports remain in `final_draft_audit/` for provenance. The numbered
guides above and `verification/` are the current entry points.

## Run the dimension-182 certificate

From the repository root:

```sh
python3 lean_arXiv_2607.15210/final_draft_audit/certify_k182_exact.py
```

This certificate needs only Python's standard library. It uses exact rational
intervals, integer square-root bounds, and a logarithm series with a proved
remainder. At t = 27/100000, its certified scalar gap exceeds
477/1000000 nats. [K182Numerics.lean](K182Numerics.lean) independently proves the
real-logarithm inequality in Lean.

The general minimizer reduction is proved in [Lemma C.1](results/C_1.md).
[Proposition VI.1](results/VI_1.md) connects the exact certificate to the actual
matrix entropy minimum and to finite channels. The conclusion is
k_high(1) ≤ 182; minimality of 182 is not claimed. The other Python programs
are numerical cross-checks, not Lean proofs.

## Citation

For this verification project, use:

```bibtex
@misc{wu_lean_2607_15210,
  author       = {Wu, Peixue},
  title        = {{Lean verification for counterexamples to additivity of minimum output p-Renyi entropy}},
  howpublished = {\href{https://github.com/pxwu24/superadditivity-of-classical-communication/tree/main/lean_arXiv_2607.15210}{Github Repository}}
}
```

Load `\usepackage{hyperref}` in your LaTeX preamble. The clickable bibliography
label is “Github Repository”. Verification records identify the checked source
files and dependency versions.
