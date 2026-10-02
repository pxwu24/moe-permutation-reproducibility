# Work toward unconditional block-modified strong convergence

**The general theorem is not yet proved.** `CanonicalStrongInput` remains an
explicit hypothesis of the paper's random-channel theorems. None of the
results below removes that hypothesis for the output dimensions used in
the nonadditivity construction.

## Install and check

Follow the [project installation instructions](../README.md#install-and-verify),
then run from the repository root:

```sh
bash lean_arXiv_2607.15210/verify-all.sh
```

The verifier rebuilds these sources together with the existing paper proofs
and audits their transitive axioms. The recorded outputs are in
[verification/](../verification/).

## Unconditional results

| Result | Main declaration | Entry file |
| --- | --- | --- |
| Full existing block-convergence interface when k = 1 | `ProjectionChannels.canonical_fullBlockModifiedStrongInput_one` | [StrongConvergenceScalar.lean](../StrongConvergenceScalar.lean) |
| Unmodified projection: affine norms and all continuous spectral tests, every k > 0 | `ProjectionChannels.ScalarStrong.canonical_projection_scalar_strong` | [StrongConvergenceScalarProjection.lean](../StrongConvergenceScalarProjection.lean) |
| Actual first Haar compression moment | `ProjectionChannels.Canonical.normalized_first_moment_tendsto` | [StrongConvergenceHaarMoment.lean](../StrongConvergenceHaarMoment.lean) |
| Exact finite Haar quadratic moments and weighted variance | `ProjectionChannels.HaarMoment.weighted_diagonal_variance` | [StrongConvergenceHaarVarianceResult.lean](../StrongConvergenceHaarVarianceResult.lean) |
| Summable variance for the actual canonical compression | `ProjectionChannels.Canonical.normalizedCompressionTrace_variance_le` | [StrongConvergenceCanonicalVariance.lean](../StrongConvergenceCanonicalVariance.lean) |
| Almost-sure first-moment convergence on one event for every real coefficient vector | `ProjectionChannels.Canonical.ae_normalizedCompressionTrace_tendsto_all` | [StrongConvergenceHaarFirstMomentAE.lean](../StrongConvergenceHaarFirstMomentAE.lean) |
| Actual expected second compression moment, every k >= 2 | `ProjectionChannels.Canonical.normalized_second_moment_tendsto` | [StrongConvergenceHaarSecondCompression.lean](../StrongConvergenceHaarSecondCompression.lean) |
| Deterministic tensor matrix units have a joint strong limit | `StrongConvergenceBlock.tensorUnits_stronglyConverge` | [StrongConvergenceBlockMatrixUnits.lean](../StrongConvergenceBlockMatrixUnits.lean) |
| Uniform compact spectral bound for every projection compression | `StrongConvergence.projection_compression_norm_le` | [StrongConvergenceCompressionBounds.lean](../StrongConvergenceCompressionBounds.lean) |
| Fixed moments and weak spectral convergence do not imply norm convergence | `StrongConvergence.spikeMatrix_weak_spectral_limit`, `spikeMatrix_norm` | [StrongConvergenceOutlier.lean](../StrongConvergenceOutlier.lean) |

The unmodified projection limits hold for every unitary sample. The first
Haar compression moment also converges almost surely, on one event for every a:

\[
\frac{1}{n}\operatorname{Tr}S_n(a)
\longrightarrow t\sum_i a_i\qquad\text{almost surely}.
\]

The proof derives Haar quadratic moments from permutation invariance and
explicit two-coordinate real and imaginary unitary rotations. For the
normalized trace q_n, it proves the actual estimate

\[
\mathbb E\bigl[(q_n-\mathbb E q_n)^2\bigr]
\leq\frac{\sum_i a_i^2}{k n^2}
\]

and applies Borel–Cantelli. Lean indexes the positive input dimension by n+1.

The exact finite Haar calculation also proves

\[
\frac{1}{n}\mathbb E\operatorname{Tr}(S_n(a)^2)
\longrightarrow
t^2\left(\sum_i a_i\right)^2+
\frac{t(1-t)}{k}\sum_i a_i^2.
\]

This second-moment limit is in expectation. Almost-sure convergence of the
second spectral moment would additionally require a concentration argument.

The k = 1 result includes signed coefficients, arbitrary scalar shifts,
output-unitary rotations, and bounded continuous test functions. The paper
needs k >= 2, where the compression is no longer a scalar multiple of the
original projection.

## Proved reductions with explicit hypotheses

These are intermediate theorems. Their hypotheses still need to be proved
for Haar block compressions before the general result becomes unconditional.

| Step | What is proved | Entry files |
| --- | --- | --- |
| Block modification | Every square complex-linear block map is a fixed matrix-unit sandwich polynomial; polynomial substitution preserves joint strong convergence. | [Polynomials](../StrongConvergenceBlockPolynomials.lean), [Modification](../StrongConvergenceBlockModification.lean), [Compression](../StrongConvergenceBlockCompression.lean) |
| Moments to weak convergence | Common compact support and convergence of all normalized trace moments give actual continuous spectral-test convergence. A countable moment event suffices for all continuous tests. | [Moments](../StrongConvergenceMoments.lean), [Empirical measures](../StrongConvergenceMomentMeasures.lean), [Matrices](../StrongConvergenceMomentMatrices.lean) |
| Almost-sure convergence | Summable deviation probabilities or second-moment bounds give simultaneous convergence for countably many tests; Lipschitz continuity extends this to all parameters and uniformly over compact parameter sets. | [Probability](../StrongConvergenceProbability.lean), [Second moments](../StrongConvergenceProbabilityMoments.lean), [Dense parameters](../StrongConvergenceProbabilityDense.lean) |
| Lower norm bound | Weak spectral convergence forces the eventual norm to exceed every smaller value than the limiting support norm. | [Lower bound](../StrongConvergenceNormLower.lean) |
| Upper norm bound | Markov's inequality and Borel–Cantelli turn summable expected high-even-trace ratios into almost-sure upper norm bounds. | [Finite norm bound](../StrongConvergenceNorm.lean), [Random matrices](../StrongConvergenceNormProbability.lean) |
| Norm and spectral-test assembly | Actual normalized trace-moment convergence and summable expected high-even-trace estimates imply both norm convergence to the support norm and all continuous spectral-test limits, on one probability-one event. | [Assembly](../StrongConvergenceMomentStrong.lean) |

The assembly theorem concerns the norm of the matrix itself. To obtain the
standard strong-convergence conclusion for every polynomial, its hypotheses
must also be established for those polynomials.

The last step uses the finite-matrix inequality

\[
\mathbb P\{\|M_n\|\ge R\}
\le R^{-2q_n}\mathbb E\operatorname{Tr}(M_n^{2q_n}),
\]

with a moment order allowed to grow with dimension. Establishing a summable
right-hand side for every R above the proposed limiting norm is the remaining
upper-edge problem. Merely knowing each fixed-order moment limit is insufficient:
the formalized example `diag(2,0,...,0)` has limiting empirical law delta_0
while its operator norm is always 2.

## Remaining mathematical work

1. Prove the limiting mixed-moment law for Haar projections and tensor matrix
   units, and identify the compression's inverse-Cauchy germ with the Bernoulli
   free-sum germ used by `IsBernoulliFreeSumLaw`. The first and second moment
   calculations do not identify that law.
2. Prove sharp high-degree moment estimates or resolvent estimates that exclude
   eigenvalues outside the limiting support. The probability and norm lemmas
   above make the required quantitative implication explicit, but do not
   establish those Haar estimates.
3. Combine those results to prove the existing `FullBlockModifiedStrongInput`
   for every required k and t, then remove the input parameter from the paper
   theorems and rerun the complete audit.

An alternative route is to formalize Haar joint strong asymptotic freeness
and free compression. The published block-modification proof uses those
substantial results; polynomial closure alone is not a proof of the random
theorem. When applying joint strong freeness through a reference projection,
joint convergence with the tensor matrix units also needs justification.

## Primary references

- [Nechita, Section 5, Theorem 5.2](https://arxiv.org/html/1802.00067v2#S5):
  block modification by a fixed polynomial and its distributional input.
- [Collins–Male, Theorem 1.4](https://arxiv.org/pdf/1105.4345): joint strong
  asymptotic freeness of Haar matrices and an independent strongly convergent
  family.
- [Arizmendi–Nechita–Vargas, Section 2.4 and Theorem 5.1](https://arxiv.org/pdf/1508.05732):
  corner-block cumulants and the limiting block-modification law.
- [Collins–Śniady, Haar integration](https://arxiv.org/abs/math-ph/0402073):
  finite Haar moment formulas underlying a possible direct approach.

The [source index](source_index.json) lists all new Lean modules and their
complete local import closures. The [status record](status.json) records
which convergence assertions remain open.

The main [project citation](../README.md#citation) points to the checked source
snapshot. Successful compilation of the reductions above must not be reported
as unconditional verification of the general random-matrix theorem.
