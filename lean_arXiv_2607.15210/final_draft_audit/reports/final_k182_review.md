# Audit of the dimension-182 result in the final draft

Audited source: `upload/Pasted text(20261002-051404).txt`, lines 1393–1477 and 2394–2563; attached `certify_k182.py`; prior repository `K182Dual.lean`, `K182Numerics.lean`, `K182Entropy.lean`, and `K182Audit.lean`.

## Mathematical conclusion

The stated dimension-182 certificate is correct, conditional on the paper's previously established output-set and Bell-output limits. The conclusion is `k_high(1) <= 182`, as the final draft now states. The argument does not exclude dimensions 2 through 181 and does not supply an explicit finite input dimension.

The exact lower bound certified independently is

```
0.00047756110230383259375495
  < 2 h_182(162513/1000000) - S_1(lambda_Bell)
  < 0.00047756110230383259375496.
```

Thus the claimed rational margin `477/1000000` is valid.

## Minimizer reduction

The four-step analytic proof is sound.

1. The angle formula gives the stated coordinate bound. The strict inequality `(k-1)t>1/k` excludes vectors with at most one positive coordinate. A small nonconstant perturbation of the zero-cost point produces entropy strictly below `log k`.
2. The perturbations excluding zero coordinates are of the correct orders. For unequal positive coordinates, transferring epsilon lowers entropy at order epsilon, while inserting `M epsilon^2` into a zero coordinate costs only `O(epsilon^2 |log epsilon|)` in entropy and creates an adjustable negative order-epsilon change in cost. For equal positive coordinates, the transfer lowers entropy at order epsilon squared, while inserting `M epsilon^4` creates the corresponding negative order-epsilon-squared cost change. Fix M first and then choose epsilon small. All positive coordinates stay in the open interval `(0,1/4)`.
3. The active constraint is regular. The nonnegative multiplier follows from the first-order necessary condition for the inequality constraint; it is strictly positive because a zero multiplier forces all coordinates equal.
4. The function `sqrt(v)*(1-v)^(3/2)` is strictly increasing on `(0,1/4)`. Consequently `f_mu` decreases and then increases, so a nonuniform stationary point has two coordinate values a<b and `f_mu'(b)>0`. A repeated high coordinate gives a negative second variation in the tangent direction `e_i-e_j`, contradicting constrained minimality. Averaging permutations of the remaining coordinates at a largest-coordinate maximizer gives the final equality of the entropy minimum with `h_k(L*)`.

One wording clarification is recommended: in the phrase “the Lagrangian `F+(mu/s)C`”, specify that `s=s(u)` is evaluated at the minimizer and `mu/s(u)` is a constant multiplier. For the particular tangent direction used, the sum is constant anyway, so the displayed second derivative is correct as written. The scalar certificate should explicitly retain `t>1/k^2` (already in the output-body setup), which ensures positive mass when normalizing.

## Python certificate

The attached mpmath script ran successfully. Its interval computations use `iv.dps=60`, but its comparison thresholds are made with ordinary `mpf`, whose precision remains at the default. Therefore the comparisons do not, on their own, certify the *exact decimal endpoints printed in the paper*. The actual printed bounds are correct; the issue is the comparison implementation.

The replacement `final_k182/certify_k182_exact.py` uses only exact `fractions.Fraction` arithmetic. Square roots are enclosed by integer square roots on a rational grid; logarithms are enclosed by an explicit positive atanh series remainder after exact power-of-two range reduction. Every endpoint comparison is exact. It uses exceptions rather than assertions, so `python -O` retains every check.

The certificate passed with 48 log-series terms and 70 square-root grid digits. It also passed under `python -O` with 24 terms and 40 grid digits. These are independent numerical runs; the Python result is not described as a Lean proof.

## Lean coverage and remaining gap

The earlier `K182Dual.lean` proves the scalar dual upper bound, exact square-root rational estimates, negativity of the dual certificate, positivity of normalization mass, the coordinate bound below 1/4, and the largest normalized eigenvalue bound. `K182Numerics.lean` proves the rational entropy gap using real-log enclosures. `K182Entropy.lean` proves the one-high entropy identity, monotonicity, and the consequences of a one-high minimizer.

The new `K182ShapeCalculus.lean` (also available as `Entropy/K182MinimizerTools.lean`) proves the exact numerical hypotheses of the minimizer lemma and the strict monotonicity used in Step 4. Its polynomial factorization proof does not rely on numerical approximation.

**The full minimizer-shape theorem is still not formalized.** In `K182Entropy.lean`, `entropy_gap_of_one_high_minimizer` explicitly assumes `HasOneHighEntropyMinimizer normalizedFeasible`. The zero-coordinate exclusion, existence/sign of the constrained multiplier, and the constrained second-order necessary condition have not been discharged in Lean. The new helper lemmas do not remove that hypothesis. No complete Lean verification of the unconditional dimension-182 theorem should be claimed until this gap is filled.

## Further formalized calculus ingredient

`K182SecondVariation.lean` proves from actual derivatives that a local minimum cannot have a negative second derivative. The proof uses the derivative slope limit and the mean value theorem, rather than assuming a second-order optimality statement. Its constrained version composes a local minimum with a continuous eventually feasible curve and applies that theorem. This verifies the generic negative-curvature contradiction in Step 4. Constructing the appropriate curve on the Bernoulli cost surface and computing its second derivative remain unformalized. Both theorem closures contain only the three standard Lean axioms.

## Audit of the interval implementation

The interval multiplication checks all four endpoint products, so mixed signs are handled correctly. Reciprocal intervals exclude zero and reverse the endpoint order on each of the two sign domains. The integer square-root construction proves `lo^2 <= x <= hi^2` with nonnegative endpoints by exact integer inequalities. The logarithm range reduction uses exact powers of two; for `z in [0,1/3]`, each omitted series denominator is at least `2N+1`, giving the stated positive geometric remainder. Integer floor and ceiling produce outward decimal endpoints, including negative and near-zero values. Additional implementation checks verified eight logarithms against 100-digit mpmath, seven exact square-root enclosures, five signed decimal-rounding cases, and all grid products in nine signed interval boxes. These checks supplement, but do not replace, the exact-rational certificate.
