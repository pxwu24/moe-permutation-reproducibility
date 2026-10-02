> Historical scope/report. The current numbered results and complete Lean dependencies are listed in [the project README](../../README.md). Statements below about missing proofs describe the earlier snapshot.

# Main-result audit of the final draft

Source: `upload/Pasted text(20261002-051404).txt`, main theorem at lines 182–192 and proof at lines 1315–1362.

## Verdict and necessary correction

The stated theorem, **for each fixed p>0 there exists a pair of channels**, follows correctly from the preceding single/Bell entropy asymptotic theorems. The choices r=5 and gamma=375 are independent of p; the sufficiently large dimensions k and n are not. The coefficient comparison is correct, including p=1.

The abstract at lines 62–64 instead claims **one pair of finite-dimensional channels that works simultaneously for every p>0**. This stronger order of quantifiers is not proved. Replace those sentences by:

> In this work, we prove that for every p>0 there exists a pair of finite-dimensional quantum channels whose minimum output p-Renyi entropies violate additivity.

Uniformity in p of the error bounds and a single choice of k,n would require an additional argument, particularly as p tends to zero, one, and infinity. The present scalar coefficient inequality alone does not supply it.

The title includes p=0, whereas the new theorem and construction prove p>0. The introduction cites existing p=0 examples; if the title is meant to describe the new theorem, change it to “for all p>0”. The PDF title metadata still describes the older restricted ranges and should also be updated.

## Mathematical checks

Writing x=16, the integral identity is

    B_(p,5)(375) = 25 p integral_1^16 (16-s) s^(p-2) ds.

For p=1, the integral is 16 log(16)-15, so the identity gives exactly 400 log(16)-375. For every p>0, s^(p-2)>=s^(-2) on [1,16]. Thus

    B_(p,5)(375)-300p >= 25p(3-log16)>0.

The logarithmic inequality is certified by the exact rational Taylor sum

    exp(3) >= sum_(j=0)^5 3^j/j! = 92/5 > 16.

The finite-dimensional passage is valid for each fixed p: first choose k so that the positive leading coefficient dominates the k-dependent remainder, then choose n so that the convergent entropy gap is positive. The condition k>=20 indeed guarantees k>=r=5 and 1/k^2<1/376. Equality of the conjugate channel's minimum output entropy follows because complex conjugation bijects input states and preserves output spectra. The Bell input supplies the required upper bound on product-channel minimum entropy.

The optional threshold discussion is also correct: for fixed 0<p<1, B_(p,r)(gamma)/(p gamma) tends to 1/(1-p); for p>=1 it tends to infinity. Consequently r=4 suffices for each fixed p>0 with gamma depending on p. Choosing r=5 allows the same gamma=375 for all positive orders, while the channel dimensions still depend on p.

## New Lean coverage

`Entropy/MainCoefficient.lean`:

- `power_remainder_lower`: for every p>0, p!=1 and x>=1, proves (x^p-1-p(x-1))/(p(p-1)) >= x-1-log x. The proof uses two derivative monotonicity arguments; it does not assume the integral representation.
- `log_sixteen_lt_three`: rational Taylor certificate above.
- `two_le_log_sixteen`: a convenient strict lower bound used at p=1.
- `main_coefficient_gap`: proves the exact quantitative lower bound above, for every real p>0, including p=1.
- `main_coefficient_strict`: proves Bpr p 5 375 > 300 p.

`Entropy/MainSpectral.lean`:

- `strict_gap_from_errors`: explicit remainder arithmetic.
- `spectral_nonadditivity_all_orders`: **unconditional spectral theorem**, using the already proved `single_output_infimum` and `bell_output`. For every p>0, all sufficiently large integer k>=20 satisfy

      entropy(explicit antisymmetric Bell spectrum at t=1/376)
        < 2 * infimumOutputEntropy(p,1/376,k,5).

  The infimum is the actual `sInf` over the explicit normalized eigenvalue body and shuffled spectra, not an assumed numerical asymptotic.
- `eventual_nonadditivity_from_limits`: explicitly conditional transport lemma for real sequences. It assumes convergence to the single/Bell limits, the Bell-input upper bound for product minimum entropy, and equality of conjugate/single minimum entropy. It does **not** define or construct quantum channels.

All eight new public declarations compile with Lean 4.19.0 and the pinned mathlib. Their printed axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, added axioms, or admitted coefficient/asymptotic facts are present.

The remaining operator/channel identification and probabilistic existence bridge are outside these two modules. Therefore this contribution must not be described as a standalone Lean proof constructing a pair of quantum channels.

## Python checks

`verify_main_coefficient.py` independently compares the closed coefficient with the integral at 100 decimal digits for 17 positive orders, including 10^-40 and values 10^-30 away from 1. All checks pass. It also verifies the rational number 92/5>16 exactly. The sampled checks are not a universal proof; that is supplied by the Lean coefficient theorem.

Generated evidence:
- `main_coefficient_results.json`
- `validation/main_coefficient_lean.log`
- `validation/main_spectral_lean.log`

Dependency for Python: mpmath (tested 1.4.1). Lean imports additionally use `Mathlib.Analysis.SpecialFunctions.Pow.Deriv` and `Mathlib.Analysis.Calculus.Deriv.MeanValue`.
