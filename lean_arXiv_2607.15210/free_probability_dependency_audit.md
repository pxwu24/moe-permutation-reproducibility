# Free-probability dependency audit

Audit date: 2026-09-29. Installed mathlib: commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, Lean `v4.19.0`.

## What is present locally

| Required ingredient | Installed source / status |
| --- | --- |
| Haar measure on locally compact groups | `Mathlib/MeasureTheory/Measure/Haar/Basic.lean`: `MeasureTheory.Measure.haarMeasure`, left invariance, regularity, normalization, and uniqueness. `Haar/Unique.lean` provides further uniqueness/invariance results. |
| Algebraic unitary group | `Mathlib/LinearAlgebra/UnitaryGroup.lean`: `Matrix.unitaryGroup`, membership and inverse formulas. This is not itself a Haar random-matrix theory. |
| Classical independent random variables | `Mathlib/Probability/Independence/Basic.lean` and adjacent files. Classical independence is different from free independence. |
| Gaussian scalar measure | `Mathlib/Probability/Distributions/Gaussian.lean`; finite products can be constructed using the measure product API. |
| Finite-dimensional Hermitian spectra | `Mathlib/LinearAlgebra/Matrix/Spectrum.lean`, matrix positive-definiteness, ranks, and adjoints. |
| C*-algebra spectra and continuous functional calculus | `Mathlib/Analysis/CStarAlgebra/Spectrum.lean` and `ContinuousFunctionalCalculus/`. |
| Bochner integrals, Dirac measures, finite mixtures | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`, including `integral_add_measure`, `integral_smul_measure`, and `integral_dirac`. |
| Lebesgue--Stieltjes measures | `Mathlib/MeasureTheory/Measure/Stieltjes.lean`. These are measures obtained from monotone functions, not the Cauchy--Stieltjes transform or its inversion theorem. |
| Ordinary convolution of measures | `Mathlib/MeasureTheory/Group/Convolution.lean`. This is classical convolution, not free additive convolution. |
| Algebraic free products | `Mathlib/LinearAlgebra/FreeProduct/Basic.lean`. This does not supply the reduced free product of tracial C*-probability spaces with positivity, faithful state, and operator norm. |

## What was not found locally

Full source scans, including bounded searches for `free probability`, `free
independence`, `freely independent`, `RTransform`, `R_transform`,
`CauchyTransform`, `cauchy_transform`, `Stieltjes inversion`, `asymptotic
freeness`, `Collins-Male`, `block-modification`, `Voiculescu`, and
`noncommutative probability`, found no relevant definitions or results.
The installed `Mathlib/Probability` tree contains no occurrence of the word
`free`. This is evidence about this pinned installation, not a claim that
no private or later formalization exists.

In particular, this installation does not provide a ready theorem for:

1. free independence of noncommutative random variables;
2. reduced free products and their tracial state;
3. free additive convolution as a probability measure;
4. its analytic R-transform and linearization identity;
5. Cauchy--Stieltjes inversion and spectral support identification;
6. strong convergence in noncommutative distribution;
7. Haar-unitary strong asymptotic freeness;
8. the block-modification limit theorem.

## Exact missing research input

The manuscript invokes Nechita, arXiv:1802.00067v2, Theorem 5.2, whose
proof invokes Collins--Male, Theorem 1.4. The needed conclusion is
almost-sure convergence of BOTH normalized traces and operator norms of
noncommutative polynomials in a Haar-invariant matrix and fixed matrix
units. Convergence of scalar moments alone does not establish the norm
limit and does not rule out spectral outliers.

After that norm-convergence theorem, a complete formalization must still
identify the block-modified limiting law using the Choi eigenvalues and
their multiplicities (Arizmendi--Nechita--Vargas, Theorem 5.1), prove the
R-transform addition/dilation identities, and prove that the continued
inverse branch identifies the actual right edge of this probability
measure. The scalar Legendre identities already checked in this project
do not establish any of these free-probability inputs.

Replacing these results by structure fields, hypotheses asserting the
desired convergence, or custom axioms would yield a conditional theorem;
it would not fulfill a request to prove the research input itself. No
such replacements were added as part of this audit.

## Public formalizations checked

The following are primary project pages, inspected on the audit date:

- [Lean's Wigner semicircle evaluation problem](https://lean-lang.org/eval/problems/wigner_semicircle/)
  describes the missing Stieltjes-transform/random-matrix framework and
  displays its target theorem with `sorry`. This is a benchmark target,
  not a completed proof that can supply an import.
- [statopia/statlean4](https://github.com/statopia/statlean4) documents
  explicit mathematical axioms for Marchenko--Pastur ingredients,
  including Stieltjes inversion and the fixed-point law. Those are not
  proved source dependencies for the requested unconditional result.
- [hanyi162013-Yihan/random-band-circular-law-lean](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean)
  contains substantial adjacent random-matrix formalization, but its
  published scope explicitly keeps the Bandeira--Boedihardjo--van Handel
  Gaussian/free comparison as an external mathematical premise. Its
  stated results concern circular laws and do not supply Collins--Male
  Haar-unitary strong asymptotic freeness or the needed block-modification
  theorem. The project is pinned to Lean 4.33.0, so it is not a drop-in
  import to this Lean 4.19.0 environment either.
- [Finite free information theory task proposal](https://github.com/harbor-framework/terminal-bench-science/discussions/559)
  describes an adjacent finite-polynomial formalization task. Finite
  free polynomial convolution is distinct from the analytic
  C*-probability and strong Haar-matrix limit theory required here.

Search did not locate a public, audited, unconditional formal proof of
the missing research input. Search non-discovery is not proof of global
nonexistence.

## Work added without assuming these gaps

`CauchyBernoulli.lean` now constructs actual Bernoulli probability measures,
their Bochner Cauchy transforms, atomic moments, and rational transform
identities. It also proves Cauchy-transform dilation, off-real-axis
integrability, the Poisson-kernel imaginary-part identity, and positivity,
strict decrease, a quantitative bound, and decay to zero on the real
half-line to the right of an almost-sure support bound. These theorems
were compiled with the pinned environment above. Their kernel axiom
audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

These are foundational proofs, not a replacement for free convolution,
spectral-edge identification, or the Haar strong-convergence theorem.

## Direct audit of the strong-convergence obstacle

The proof in Section 3 of
[Collins--Male, arXiv:1105.4345v2](https://arxiv.org/pdf/1105.4345)
was inspected directly. Its Haar-unitary conclusion is obtained by a
spectral coupling with a Gaussian ensemble. The starting result is its
Theorem 1.3, the strong convergence of GUE matrices together with an
independent deterministic family. Consequently, transcribing the short
coupling argument would still leave that substantial norm-convergence
theorem unproved. Nechita's Section 5 uses this strong convergence when
expressing a block modification as a polynomial involving matrix units.

The following is an analysis of the specialized problem, not a theorem
already established in this Lean project. Write

`S_n(a) = sum_i a_i P_{ii}^{(n)}`,
`b = 1 + sum_i |a_i|`, and `B_n = S_n(a) + b I`.

Then `B_n` is positive definite, with a deterministic norm bound. Let
`r` be the proposed right edge and `L = r + b > 0`. A concrete missing
estimate which WOULD settle the upper-edge problem is: for each
`epsilon > 0`, obtain constants `C_epsilon`, `N_epsilon` and integers
`p_n >= c_epsilon log n` such that, for every `n >= N_epsilon`,

```
E [ tr_n (B_n ^ p_n) ] <= C_epsilon (L + epsilon/2) ^ p_n,
c_epsilon >= 3 / log ((L + epsilon)/(L + epsilon/2)).
```

Indeed, Markov's inequality and positivity would give

```
Pr [lambda_max(S_n(a)) >= r + epsilon]
 <= n E[tr_n(B_n^p_n)] / (L + epsilon)^p_n
 <= C_epsilon n^(-2).
```

Borel--Cantelli would then exclude outliers almost surely. The lower
edge inequality would follow from almost-sure convergence of the
empirical measures and positive limiting mass arbitrarily near `r`.

The missing step is precisely the uniform high-moment estimate at
logarithmically growing order, with the correct exponential scale `L`.
Fixed-order Haar/Weingarten expansions do not imply it. An error of the
form `C^p/n^2` with `C > L` also does not automatically suffice: the
large value of `c_epsilon` required as `epsilon` becomes small can make
that error dominate. Sharp genus/control estimates or an equivalent
matrix-resolvent no-outlier argument would have to be proved.

Concentration on the unitary group supplies a different incomplete
route: it can force the largest eigenvalue close to its median or
expectation, but does not identify the limiting median or expectation.
The possible existence of finitely many outliers is invisible to the
empirical measure. Thus concentration plus convergence of fixed-order
moments does not close the gap either.

For the Gaussian realization `P = G(G*G)^(-1)G*`, the same issue becomes
a strong-limit problem for a rational matrix expression in Gaussian
blocks. A full Gaussian matrix-resolvent/local-law theory would provide
another possible route, but that theory is not already proved in this
project or available in the inspected mathlib installation.

No unconditional high-moment estimate of the displayed strength, no
replacement local law, and no full Collins--Male proof has been
obtained in the current work. No definition, hypothesis wrapper, or
axiom was added to conceal this remaining research input.
