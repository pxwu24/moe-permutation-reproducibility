# Paper-to-Lean coverage

This map refers to *Explicit channels with unbounded gains in classical
communication using entangled inputs*. It was aligned on 2026-09-29 with the
attached final-letter and supplemental LaTeX fragments. Their exact SHA-256
hashes are recorded under `current_manuscript_sources` in
[`source-provenance.json`](source-provenance.json). The earlier 19-page PDF
and recovered original-source hashes remain there for historical provenance.

The attached final subsection omitted the definition and proof of the
postprocessing map. The complete construction remains in Lean and in
[`../supplement/main_theorem.tex`](../supplement/main_theorem.tex); it is
necessary for the main theorem. See [the revision notes](PRL_REVIEW_2026-09-29.md).

All active proofs below belong to the unified `entropy/` project, using Lean
4.33.0. [`entropy/AllProofs.lean`](entropy/AllProofs.lean) is the entry point.
The original `adder-trace/` project remains available on Lean 4.24.0.
The current manuscript numbers the uniform measurement and filter trace
estimates as Propositions 2 and 3. Older source comments and the legacy
`SupplementAdder.proposition4_trace_bound` alias retain the previous numbering;
the mathematical trace statement is unchanged.

## Supplement results

| Result | Principal source | Principal declarations |
| --- | --- | --- |
| Lemma 3: single-copy entropy and Hilbert–Schmidt bounds | `SupplementSingle.lean` | `SupplementSingle.lemma3`, `single_copy_hilbertSchmidt_bound` |
| Lemma 4: two-copy Bell-input entropy sandwich | `SupplementEntropy.lean` | `SupplementEntropy.lemma4` |
| Corollary 1: tensor-coordinate entropy estimate | `SupplementEntropy.lean` | `SupplementEntropy.corollary1` |
| Corollary 2: linear and unbounded entropy gap | `SupplementEntropy.lean` | `SupplementEntropy.corollary2`, `corollary2_unbounded` |
| Proposition 2: uniform measurement estimate | `ActualGridSupport.lean` | `ActualGridSupport.actual_grid_support_bound` |
| Proposition 3: complete-grid filter trace estimate | `AdderTrace.lean` | `AdderTrace.technical_trace_bound` |
| Lemma 5: word trace estimate | `SupplementAdder.lean` | `SupplementAdder.lemma5_word_trace` |
| Lemma 6: matrix moment estimate | `SupplementAdder.lean` | `SupplementAdder.lemma6_moment_bound` |

## Main theorem and construction

| Step | Sources and endpoints |
| --- | --- |
| Actual adder circuit, tensor matrices, finite input labels, unitarity and reality | `MainAdderTuple.generator_circuit`, `generator_unitary`, `generator_real`, `tensorAdderMatrix_eq_tuple`, `enumeratedTuple_eq_finAdderMatrix` |
| Exact table parameters, logarithmic ceilings, modulus bound, trace error below `10⁻⁶` | `MainFilterParameters.prescribedFilter_small`, `L_pos`, `Q_wordBound`, `a_identity` |
| Equality of both grid/filter representations and invariance under input relabeling | `MainGridBridge.fullGridFilter_mat`, `enumerated_fullGridFilter_small` |
| Measurement-and-feedforward map is CPTP, with the prescribed matrix-entry formula | `MainChannel.fullGridChannel`, `fullGridChannel_entry` |
| Entrywise reality, so the two-copy estimate applies to the channel paired with itself | `MainReal.fullGridChannel_real`, `MainBasic.two_copy` |
| Unconditional basic-channel estimates for `r ≥ 1` | `MainConcreteBasic.single_copy`, `two_copy` |
| Finite-field trace-character orthogonality, polynomial root bound, and Pauli contraction | `MainRandomizer`, `MainPauli.fieldSeed_contraction`, `MainConcreteRandomizer.contraction` |
| Randomizer seed count and exact numerical gap certificate | `MainConcreteRandomizer.seed_count_bound`, `MainParameters.numerical_margin`, `fixed_signal_gap` |
| Entropy after output randomization and entropy cost of a finite mixture | `MainSmoothing`, `MainFlaggedEntropy`, `MainSmoothedChannel`, `MainConcreteSmoothed.single_copy`, `two_copy` |
| Holevo supremum, classical Pauli completion, and the two-copy Bell-and-Pauli ensemble | `MainHolevo`, `MainHolevoTensor`, `MainPauliHolevo.completion_holevo_upper`, `completion_tensor_holevo_lower` |
| Revised sharp asymptotic slope, actual Bell-output entropy bound, and completed-channel Holevo bound | `MainSharperPostprocessing.numerical_margin_sharp`, `two_copy_sharp`, `holevo_two_copy_sharp` |
| Both strict Holevo inequalities for the defined channel, for every real `N ≥ 1` | `MainTheorem.main_theorem` |
| Exact input/output cardinalities and exponential/doubly exponential dimension bounds for that same channel | `MainTheorem.input_card`, `output_card`, `main_dimensions` |
| Parameter-table asymptotics as actual `Asymptotics.IsTheta` statements | `MainParameterGrowth.log_P_theta`, `L_theta`, `q_theta`, `log_Q_theta`, `C₂_theta`, `log_inputDimension_theta`, `log_outputDimension_theta` |
| Capacity lower bound from actual tensor powers and the regularized Holevo supremum | `MainCapacity`, `MainCapacityCorollary.main_capacity_gap`, `unbounded_capacity_gap` |

`MainTheorem.channelFor` defines the final CPTP map. The only premise of
`MainTheorem.main_theorem` is `1 ≤ N`: the proof does not take trace, entropy,
randomizer-contraction, or Holevo bounds as unproved hypotheses. The fixed
choice is `r = 10^11 * Nat.ceil N`.

## Interpretation and scope

- The entropy statements concern actual density matrices and von Neumann
  entropy from Physlib. The general Supplement statements retain the
  hypotheses appearing in the paper. Channel-entry and conjugate-entry
  identities specify the channel definitions; coordinate marginal identities
  are derived, for arbitrary complex unitary factors.
- The one-copy Hilbert–Schmidt estimate holds for every input density matrix,
  which is the pointwise form of the paper's supremum bound.
- Proposition 2 is proved for arbitrary finite matrix families. The full grid,
  finite filter sum, and inverse-square-root measurement operator are actual
  definitions. `MainGridBridge` identifies them with the adder trace model.
- The adder computational basis consists of residue-pair tuples, of cardinality
  `Q^(2*r)`. `MainAdderTuple` proves the finite-basis identification used in the
  entropy project. The output enumeration in `ActualTensorBasis.eOut` was
  aligned with `AdderTrace.indexEquiv.symm`; this changes only label selection.
- Lemma 5 branches on the actual modular permutation matrix being the identity
  and covers all word lengths from 1 to `4*L`. Lemma 6 has the stated common
  Hilbert–Schmidt factor. Its formal proof uses finitely supported reduced-word
  convolution to establish the inequality; it does not reproduce every step of
  the manuscript's finite-compression presentation.
- The finite-field randomizer is defined using Mathlib's `GaloisField 2 t`,
  with field trace, explicitly prescribed Pauli exponents, and all seed pairs.
  The contraction and seed-count proofs are independent of the polynomial
  representation. The implementation of the lexicographically first monic
  irreducible binary polynomial, and executable conversion to that specific
  representation, are not formalized here. No field-bias estimate is assumed.
- `MainHolevo.holevo` is a supremum over finite input ensembles.
  `MainCapacity.regularizedHolevoCapacity` is the supremum of the normalized
  Holevo quantities of actual tensor powers. The capacity-gap corollary is
  proved for this regularization. Its operational interpretation uses the
  standard coding theorem identifying regularized Holevo information with
  classical capacity; that coding theorem is not re-proved in this collection.
- Ordered matrix-trace inequalities use the real part of the complex trace.
  Hermitian trace-reality results justify that convention. All logarithms are
  natural, and Hilbert–Schmidt norms are unnormalized.

## Note on the written proof of Lemma 5

Cancelling adjacent inverse letters alone does not make every interior power
of `P` nonzero: adjacent equal indices with the same sign can remain, as in
`T_i T_i`. Before the cone argument, group each maximal run of equal indices
into one nonzero power of `T_i`. Consecutive grouped indices are then distinct.
Keep the original signed-letter list for the quantitative length bound.
The formal proof proves the stated bound without the problematic intermediate
claim and without changing its constants.

## Verification records

Run `bash lean/verify-all.sh` from the repository root. The default verifies the
entire unified Lean 4.33 project. Set `VERIFY_LEGACY_ADDER=1` to also replay the
preserved Lean 4.24 adder project.

The verifier compiles every local proof source and audits all declarations
originating in those modules, following their axiom dependencies transitively.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Source scans
alone are not treated as Lean verification.

The historical aggregate result for the unchanged 57-module project is
`entropy/verification/verification_status.json`, with the compiler log,
axiom-audit log, and exact source manifest in the same directory. A success
record is generated only after both the complete build and audit pass. That recorded combined run passed: all **57 local proof modules** were rebuilt,
and all **2,048 originating declarations** passed the transitive axiom audit.
The process exited with code 0. Only the three standard axioms listed above
occur; there are no proof placeholders or additional mathematical axioms.

`source-provenance.json` retains all recovered original-source hashes and
records the Lean 4.33 adder ports and the enumeration adjustment. Historical
Lean 4.24 records remain under `adder-trace/verification/`.

## Revised coefficient (2026-09-29)

`MainSharperPostprocessing` keeps the fixed prefactor `beta` outside the
r-th power. Its actual Bell-output and Holevo endpoints have slope
`d_M(s) - 2 log(1+9/M)` and explicit error
`8 log r + 4 log 108 + 2 log beta`. It also proves this slope exceeds
`5*10^-9`. The existing fully explicit main theorem and dimension statements
are unchanged. The new module is imported by `AllProofs.lean`.

The separately labelled Python numerical cross-check is
[`scripts/check_prl_parameters.py`](scripts/check_prl_parameters.py);
its output is under `verification-prl-2026-09-29/`. It is not a Lean certificate.

## Current verification result

The fresh 2026-09-29 aggregate run passed with exit code 0: **58 local proof
modules** were rebuilt from source and **2,054 originating declarations**
passed the exhaustive transitive axiom audit. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The successful source manifest
matches the current proof files, including `MainSharperPostprocessing.lean`.

Current record: [`entropy/verification-2026-09-29/verification_status.json`](entropy/verification-2026-09-29/verification_status.json).
