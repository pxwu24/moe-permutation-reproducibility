> Historical scope/report. The current numbered results and complete Lean dependencies are listed in [the project README](../../README.md). Statements below about missing proofs describe the earlier snapshot.

# Random compression formula: final-draft audit

Audited source: `upload/Pasted text(20261002-051404).txt`, lines 612–690
and 1478–1976. Existing formal sources were read from repository commit
`3495d4c5b202f5c43196e97ea4c30a8d00ca5d4b` and rebuilt in the pinned
Lean 4.19.0 / mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` environment.

## Mathematical verdict

The random compression formula and its right-edge proof are correct, given
the stated strong block-modification theorem. The four-step argument covers
negative coefficients, zero coefficients, finite critical points, and an
infimum reached only as the positive parameter tends to infinity. In
particular, the argument does not discard possible atoms at the upper edge.

The finite-endpoint argument is sound: a nonzero derivative of the analytic
inverse branch would give a real holomorphic continuation of the actual
Cauchy transform across a support point, contradicting the Poisson-kernel
mass estimate (or Stieltjes inversion). Analyticity on the entire positive
parameter axis follows from the strictly positive discriminant. At a finite
endpoint the derivative is therefore zero; the Legendre tangency identity
then identifies its value with the global dual minimum. At an infinite
endpoint the inverse branch decreases everywhere, giving the infimum
directly.

For the scalar duality, the endpoint budget is

`(#positive coefficients) * (1-t) + (#negative coefficients) * t`.

When this is at most `1/k`, the value is `sum_i max(a_i,0)`, and no positive
finite critical point exists. Equality of the endpoint budget and `1/k`
belongs to this infinite-parameter case. The prior Lean file
`BernoulliCriticalPoint.lean` proves this distinction.

## Small manuscript corrections

1. The random-compression lemma begins with one fixed projection `P`,
   dimension `n` and rank `d`, but its conclusion concerns a sequence.
   Replace its opening with:

   > Fix an integer \(k\geq1\). Let \(P_n\) be Haar-distributed
   > projections of rank \(d_n\) on
   > \(\mathbb C^n\otimes\mathbb C^k\), where
   > \(d_n/(nk)\to t\in(0,1)\).

2. The main-text proof says the Choi matrix of `φ_a` is `I_k ⊗ A` without
   announcing a convention change. Under the input-first convention of the
   preliminaries it is `A ⊗ I_k`. The appendix correctly states that the
   block-modification theorem uses the output-first convention. Add the same
   qualification in the main proof: “In the output-first Choi convention,
   \(C_{\varphi_a}=I_k\otimes A\).”

“Random compression formula” is an appropriate name: the limit is evaluated
exactly rather than merely bounded.

## Exact Lean coverage

Already present, with genuine definitions and no additional mathematical
axioms:

- `ProjectionStrongConvergence.lean`: strong convergence of projections to
  the Bernoulli law in the polynomial trace/norm sense.
- `BlockModification.lean`: the finite matrix block-modification identity.
- `PreliminariesLegendre.lean`, `BernoulliCalculus.lean`: the actual scalar
  cost, dual function, maximizing vector, derivatives and limits.
- `BernoulliDuality.lean`: full arbitrary-sign equality
  `max_D sum_i a_i u_i = inf_{w>0} K_a(w)`, including attainment on `D`.
- `BernoulliCriticalPoint.lean`: finite/infinite endpoint classification and
  uniqueness of the finite dual minimizer.
- `CauchyBernoulli.lean`, `CauchyHolomorphy.lean`: actual Bochner Cauchy
  transforms, Bernoulli transform identities, and holomorphy.
- `SpectralEdge.lean`: a real holomorphic continuation across an actual
  measure-support point is impossible, using proved Poisson-kernel bounds.
- `CauchyLocalInverse.lean`: an actual real holomorphic local inverse from
  analyticity, reflection symmetry, and a nonzero derivative.
- `CompressionSpectral.lean`, `CompressionExtension.lean`: actual matrix
  eigenvalue Lipschitz bounds and the single almost-sure event, conditional
  on fixed-parameter convergence.

New in this audit: `CompressionEndpointGlue.lean` proves three statements:

1. `cauchy_agreement_upper_of_real_right`: agreement with the actual Cauchy
   transform on a real right interval propagates into the upper half-disc.
2. `no_real_holomorphic_right_continuation_at_support`: such a continuation
   is incompatible with a point of the actual support.
3. `inverse_cauchy_finite_endpoint_deriv_eq_zero`: a finite endpoint of an
   analytic inverse Cauchy branch has zero derivative. Its hypotheses include
   convergence of the actual Cauchy transform to the endpoint and its actual
   local right-inverse relation. It does not assume the desired edge formula.

All three new declarations compile. `CompressionEndpointAudit.lean` reports
only `propext`, `Classical.choice`, and `Quot.sound`.

**The full random-compression theorem is not yet a complete Lean theorem
under only the permitted strong-convergence black box.** The missing formal
connection is construction/identification of the actual free-convolution
law, its R-transform linearization, and instantiation of its inverse-Cauchy
branch with the explicit `K_a`. Neither the old scalar-duality theorem nor
the new endpoint theorem silently discharges this connection. The existing
`UnprovedTargets.lean` explicitly labels the full random theorem as an
unproved proposition. No new axiom or `sorry` was introduced to hide this gap.

## Python checks

`random_compression_check.py` passes:

- 210 Legendre inequalities and maximizing equalities at 85 decimal digits;
- 210 arbitrary-sign duality cases: 122 finite critical parameters and 88
  infinite-parameter cases, including the equality threshold;
- six independent finite Haar-projection simulations, at input dimensions
  24, 72, 160 with output dimensions 2 and 3.

The largest scalar equality residual was approximately `1.03e-84`.
`random_compression_results.json` contains all six matrix results. These
calculations are reproducible checks, not a proof of almost-sure convergence.
The scalar global variational identity is supplied by Lean, not by numerical
optimization. Dependencies are NumPy and mpmath.
