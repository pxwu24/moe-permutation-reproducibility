> Historical scope/report. The current numbered results and complete Lean dependencies are listed in [the project README](README.md). Statements below about missing proofs describe the earlier snapshot.

# Formalization scope audit

## Output-dimension-182 extension

The new `K182Dual`, `K182Numerics`, and `K182Entropy` modules accompany
the rigorous certificate in `k182/`. Their separate scope and audit are
documented in `k182/README.md`. The scalar eigenvalue bound and the
real-logarithm numerical gap are proved in Lean; the global entropy
comparison retains an explicit minimizer-shape hypothesis. Its analytic
proof is in `k182/k182_revision.tex`, but it is not yet a Lean theorem.
The random-matrix limit gaps described below are unchanged.

## Original preliminaries snapshot

This audit compares the supplied appendix and the current `deliverables/preliminaries_revised.tex` / `appendix_revised.tex` against the actual Lean statements. It describes the current source snapshot, not a claim that every sentence of the manuscript has been formalized.

## Established results

| Manuscript component | Actual final theorem(s) | Scope |
|---|---|---|
| Choi inversion, conjugation, two tensor-order conventions | `ProjectionChannels.choi_reconstructs_linearMap`, `conjugateMap_choi`, `choi_conventions` | Finite complex matrices and actual linear maps. |
| Choi characterization of quantum channels | `ProjectionChannelsCP.completelyPositive_iff_choi_posSemidef`, `quantumChannel_iff_choi` | Complete positivity is defined through all finite amplifications; the equivalence is proved. |
| Generalized Choi normalization and rescaling | `ProjectionChannelsCP.generalizedChoi_is_quantumChannel`, `generalizedChoi_positive_rescaling` | Uses the actual positive matrix square root and inverse. |
| Full local support lemma | `HaarProjection.haar_projection_partialTrace_rank_fin`, `haar_projection_full_local_support_iff_fin` | **Unconditional finite-dimensional Haar result** under the manuscript's projection/rank hypotheses. The normalized Haar measure, Gaussian invariance, generic rank, whitening, orbit conjugacy, and law identification are proved. |
| Elementary strong convergence of the projections themselves | `ProjectionStrongConvergence.projections_strongly_converge_to_bernoulli` | Actual polynomial normalized traces and Euclidean operator norms, from the rank ratio. This is single-matrix convergence, not joint asymptotic freeness with matrix units. |
| Deterministic block modification | `ProjectionChannels.amplified_diagonalTrace`, `blockModification_polynomial`, `spectralProjection_partialTrace` | Actual block-map identity, fixed polynomial representation, and Choi spectral-projection partial traces. No stochastic limiting law follows just from these identities. |
| Scalar Bernoulli Legendre identity | `ProjectionChannels.bernoulli_legendre_maximum`, `bernoulli_legendre_equality_iff` | Exact cost and dual formulas, attainment, unique explicit optimizer. |
| Scalar calculus | `hasDerivAt_deriv_bernoulliCost_rpow`, `strictConvexOn_bernoulliCost`, `tendsto_deriv_bernoulliCost_zero`, `tendsto_deriv_bernoulliCost_one`, `hasDerivAt_deriv_bernoulliDual` | Both displayed derivatives of the cost, strict convexity, endpoint blowups, and derivatives of the explicit dual. First/second differentiability is not a proof of real analyticity. |
| Finite-dimensional convex duality | `ProjectionChannels.bernoulli_support_eq_inf`, `bernoulli_full_duality` | Unconditional equality of the actual feasible-set support function and the infimum of the explicitly defined scalar `bernoulliK`. Covers arbitrary signs and zero coefficients. |
| Critical-point classification | `bernoulliK_has_critical_iff`, `bernoulliK_unique_global_minimum`, `bernoulliK_infimum_at_infinity`, `bernoulliK_deriv_sign_around_critical` | Exact endpoint-budget criterion, unique global minimizer, strict derivative signs, and the alternative of an unattained infimum at infinity. |
| Actual Bernoulli measure and Cauchy transform | `cauchyTransform_bernoulli_rational`, `cauchyTransform_bernoulli_quadratic`, `cauchyTransform_dilation` | Actual measure and Bochner integrals; rational transform and quadratic relation. The dilation theorem concerns the Cauchy transform, not the R-transform. |
| Support obstruction to real holomorphic continuation | `ProjectionChannels.no_real_holomorphic_continuation_at_support` | Proved for the actual Cauchy transform and actual measure support. A genuine real-valued holomorphic continuation is required. This does not yet identify an inverse branch or prove `right edge = inf K`. |
| Lipschitz and simultaneous-parameter step | `blockCompression_largest_lipschitz`, `bernoulliSupport_lipschitz`, `ae_all_projection_compressions` | Both actual Lipschitz estimates are proved. The last theorem **assumes fixed-parameter almost-sure convergence** and upgrades it to a common event for every parameter. |

## Substantive claims still not proved in this project

1. **Free-probability framework and limiting-law identification.** No project definition of free independence in a tracial C*-probability space, free additive convolution, or the actual probability measure
   `μ_(a,t) = boxplus_i (D_(a_i/k) b_t)^(boxplus k)` is present. Hence the Arizmendi–Nechita–Vargas law-identification theorem is not formalized. This gap is separate from strong convergence.
2. **R-transform statements.** There is no general R-transform definition derived from a local inverse of the actual Cauchy transform, no proof of its free-additive-convolution linearization or dilation law, and no proved selection of the Bernoulli plus-sign inverse branch with the requisite behavior at zero. The quadratic relation and the formula for the scalar function `bernoulliDual` do not establish these assertions. In particular, `g_t(y)=y R_(b_t)(y)` has not been connected formally to the law's R-transform.
3. **Actual spectral-edge identification.** The present `SpectralEdge.lean` proves the no-continuation obstruction, not the manuscript's `max supp(μ_(a,t)) = inf_(w>0) K_a(w)`. The local inverse, continuation/identity-theorem argument, endpoint inverse correspondence, and use of the inverse-function theorem must still be assembled for an actual law. `CauchyHolomorphy.lean` now proves holomorphy of the actual integral, and `CauchyLocalInverse.lean` proves an actual real holomorphic local inverse. Agreement of that inverse with the Cauchy transform and the complete edge argument remain unproved.
4. **Joint random-matrix strong convergence.** Collins–Male Haar-unitary strong asymptotic freeness / Nechita's strong block-modification theorem is absent. No almost-sure norm limit or equivalent no-outlier estimate for the block compressions is proved. The complete random compression lemma is explicitly recorded only as the proposition `ProjectionChannels.randomCompressionStatement` in `UnprovedTargets.lean`; there is no theorem asserting it.
5. **Other appendix background assertions.** The compact-support weak-convergence/moment equivalence, general strong-convergence-to-spectral-edge implication, local analytic inverse construction at infinity, R-transform pole cancellation, and real analyticity of the explicit `g_t`/`K_a` have not been instantiated as proved project results. The project uses some relevant mathlib infrastructure, which should not be mistaken for a proof of these manuscript applications.
6. **Literal preliminary definitions not encoded.** Density-operator sets, the normalized Bell-vector/state relation, Rényi/von Neumann entropy and its endpoint/continuity conventions, and minimum-output-entropy definitions do not have a complete matching formal interface. The CP proof does contain an unnormalized Bell outer product. No substantive entropy theorem is stated in this preliminary section, but a claim that every definition has been formalized would still be inaccurate.

Thus **the full local-support lemma is now proved**, and **the scalar support/infimum duality is now proved**, but **the random compression lemma and its free-convolution spectral-edge interpretation remain unproved**. These must not be collapsed into the statement that only one external strong-convergence citation remains.

## Module inventory

Packaged mathematical modules (all compiled):

- Choi/matrix: `PreliminariesMatrix`, `PreliminariesChoi`, `CompletePositivity`.
- Haar/Gaussian: `GaussianRank`, `GaussianRadial`, `GaussianUnitary`, `GaussianMatrixLaw`, `GaussianWhitening`, `HaarProjection`, `HaarMeasure`, `HaarOrbitUnique`, `MatrixRankMeasurable`, `ProjectionOrbit`, `HaarLocalSupport`, `HaarFullLocalSupport`.
- Scalar/convex: `PreliminariesLegendre`, `PreliminariesAnalysis`, `BernoulliCalculus`, `BernoulliDuality`, `BernoulliEdgeCalculus`, `BernoulliCriticalPoint`.
- Compression: `CompressionSpectral`, `CompressionExtension`, `ProjectionStrongConvergence`, `BlockModification`.
- Cauchy/support: `CauchyBernoulli`, `CauchyHolomorphic`, `SpectralEdge`, `CauchyHolomorphy`, `CauchyLocalInverse`.
- Explicit unproved target: `UnprovedTargets` (a proposition definition, not a proof).
- `Preliminaries` imports `PaperFormalization`, which imports the verified modules. These entry points add no mathematical claims.

Additional `*Audit.lean` files print kernel dependencies. `Probe*`, `*Probe`, `ChoiScratch`, and `AnalysisConvergenceCheck` are development files, not additional manuscript coverage.

The audited proofs examined use no custom axioms or `sorry`. A kernel-axiom audit establishes proof integrity for the statements actually proved; it does not establish that these statements cover the entire paper.

## Delivery consistency

The archive contains the modular project, the two revised LaTeX sections, build and audit logs, and the updated scope reports. Earlier single-file/47-theorem verification notes are superseded by this snapshot. The full Haar result is proved; the free-probability gaps above remain.

