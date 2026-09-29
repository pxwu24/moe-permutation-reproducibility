# Preliminaries: revision and verification

## Mathematical conclusion

The two stated lemmas are correct. The supplied Bernoulli spectral-edge argument is also correct after the clarifications below. The formula and constants in the random compression estimate are unchanged.

1. **Choi convention.** With the manuscript's input-first convention, the map `φ_a(X) = Tr(AX) I_k` has `J_{φ_a} = A ⊗ I_k`. Nechita's block-modification theorem uses the output-first convention `C_{φ_a} = I_k ⊗ A`. The revised text defines both explicitly.
2. **Full local support.** The proof now uses a Gaussian matrix `G`, the Haar projection `G(G†G)⁻¹G†`, and its reshaping `H = [G₁ … G_k]`. Since the middle factor is positive definite, the reduced projection has rank `rank H = min(n,kd)` almost surely. No equality in law between the reduced projection and an induced random state is claimed.
3. **Uniqueness of the critical point.** The appendix now states that `F_a` is strictly increasing when `a ≠ 0`. The case `a = 0` gives `K_a(w) = 1/w` directly.
4. **Analytic continuation at the spectral edge.** The continuation must be real-valued on the real interval to conclude that the interval has zero measure. The revised proof states this condition and uses non-atomic endpoints in the Stieltjes inversion formula.

The argument covers mixed signs, zero coefficients, and the limiting minimizer at infinity, including the case of an edge atom. Fixed `k` is explicit in the compression lemma.

## LaTeX files

- `preliminaries_revised.tex`: replacement for the preliminary section.
- `appendix_revised.tex`: the supplied appendix with the proof clarifications and numbered `equation`/`align` environments.

Retain the manuscript's macros, theorem environments, bibliography keys, and surrounding sections. Both files compile together in a minimal article wrapper with `amsmath`, `amssymb`, `amsthm`, `mathtools`, `mathrsfs`, and `enumitem`. The remaining undefined references in that isolated check refer only to the supplied manuscript bibliography and to the Bell-output and entropy-asymptotics sections, which were not supplied. No overfull boxes were reported in that wrapper. This is a syntax check, not a check of the full manuscript's journal layout.

## Sources checked

- Ion Nechita, *On the separability of unitarily invariant random quantum states: the unbalanced regime*, [arXiv:1802.00067v2](https://arxiv.org/pdf/1802.00067), Definition 5.1 and Theorem 5.2. These are renumbered Definition 5 and Theorem 6 in the published HTML; the revision cites Section 5 to avoid that ambiguity.
- Octavio Arizmendi, Ion Nechita, Carlos Vargas, *On the asymptotic distribution of block-modified random matrices*, [arXiv:1508.05732](https://arxiv.org/pdf/1508.05732), Theorem 5.1.

The cited strong block-modification theorem allows Hermiticity-preserving maps. Complete positivity of `φ_a` is not required, so negative coefficients are allowed. Its Choi eigenvalue multiplicities give precisely the dilation `a_i/k` and the `k` free-convolution copies in the manuscript.

## Formal-verification boundary — expanded project

The full Haar local-support lemma is now proved in Lean, including the Gaussian rank theorem, unitary invariance, uniqueness of the Haar orbit law, whitening, and transfer of the rank event. The Choi characterization and the complete deterministic convex-duality calculation are also proved.

**The complete requested formalization is not finished.** The random compression lemma and the identification of the actual free-convolution spectral edge remain unproved. The missing work includes:

- A tracial noncommutative probability/free-independence framework, free additive convolution, and the construction/identification of the measure `μ_(a,t)`.
- The R-transform derived from the Cauchy inverse, its free-addition and dilation identities, and the identification of the explicit scalar formula with that transform.
- The complete analytic assembly proving the actual right spectral edge equals `inf_(w>0) K_a(w)`. Holomorphy of the actual Cauchy transform, a real local inverse theorem, and the obstruction to continuation through support are proved separately; their required identification and continuation argument is not finished.
- Collins–Male strong asymptotic freeness and the strong block-modification theorem, or an equivalent direct no-outlier estimate for the random compressions.
- Some background and definitional material listed precisely in `formalization_scope_map.md`, including the entropy interfaces and the general compact-support moment/weak-convergence equivalence.

None of these missing claims is introduced as an axiom or an admitted theorem. `UnprovedTargets.lean` records the random compression goal as a proposition definition only; it contains no proof of that proposition. It is not imported by the verified-results aggregate.

## Main proved endpoints

| Manuscript component | Lean theorem |
| --- | --- |
| Choi characterization with actual complete positivity over all finite amplifications | `ProjectionChannelsCP.quantumChannel_iff_choi` |
| Generalized Choi normalization and positive rescaling | `ProjectionChannelsCP.generalizedChoi_is_quantumChannel`, `generalizedChoi_positive_rescaling` |
| Haar partial-trace rank `min(n,kd)` almost surely | `HaarProjection.haar_projection_partialTrace_rank_fin` |
| Haar strict positivity almost surely iff `n ≤ kd` | `HaarProjection.haar_projection_full_local_support_iff_fin` |
| Deterministic projection polynomial trace and operator-norm convergence | `ProjectionStrongConvergence.projections_strongly_converge_to_bernoulli` |
| Actual block-map and polynomial identities | `ProjectionChannels.amplified_diagonalTrace`, `blockModification_polynomial` |
| Scalar Legendre identity with the unique explicit optimizer | `ProjectionChannels.bernoulli_legendre_maximum` |
| Feasible-set support equals the infimum of the explicit scalar function, with no assumed saturation | `ProjectionChannels.bernoulli_full_duality`, `bernoulli_support_eq_inf_nat` |
| Full finite-critical-point / infimum-at-infinity classification | `ProjectionChannels.bernoulliK_has_critical_iff`, `bernoulliK_unique_global_minimum`, `bernoulliK_infimum_at_infinity` |
| Holomorphy of the actual Cauchy-transform integral | `ProjectionChannels.differentiableOn_cauchyTransform_upper`, `differentiableOn_cauchyTransform_right` |
| Real holomorphic continuation is impossible through actual measure support | `ProjectionChannels.no_real_holomorphic_continuation_at_support` |
| Real holomorphic local inverse from analyticity, nonzero derivative, and reflection symmetry | `ProjectionChannels.exists_real_holomorphic_local_inverse` |
| Actual largest-eigenvalue and feasible-set support Lipschitz estimates | `ProjectionChannels.blockCompression_largest_lipschitz`, `bernoulliSupport_lipschitz` |
| A common probability-one event from fixed-parameter convergence | `ProjectionChannels.ae_all_projection_compressions` — fixed-parameter convergence remains an explicit hypothesis |

The scalar support/infimum equality must not be described as a proof of the free-convolution spectral-edge equality. Likewise, strong convergence of `P_n` alone does not prove joint strong convergence with the fixed tensor matrix units.

## Executed verification

The project uses Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Every packaged mathematical source is compiled. The final clean rebuild and axiom audit are recorded in `lean_verification.log` and `full_axiom_audit.log`; source hashes are recorded in `SHA256SUMS`.

`FullAudit.lean` audited 421 theorem declarations (including generated helpers). It examines every theorem declaration from the project modules, including generated and private helper theorems, using Lean's transitive axiom collector. The allowed dependencies are the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. Compiler-generated unsafe implementation artifacts are reported separately and are not theorem dependencies. The project adds no logical axiom, and no proof depends on `sorryAx`.

This audit checks the integrity of the statements actually proved. It does not establish that those statements cover the whole manuscript. See `formalization_scope_map.md` and `free_probability_dependency_audit.md` for the remaining mathematical work.
