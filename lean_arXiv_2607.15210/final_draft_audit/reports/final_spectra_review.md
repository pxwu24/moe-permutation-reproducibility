# Final-draft audit: antisymmetric spectra and entropy asymptotics

Source: `upload/Pasted text(20261002-051404).txt`, lines 1077–1307 and 2140–2393. The four entropy estimates have the correct constants and error orders, for each fixed real `p > 0`, fixed `0 < t < 1`, and fixed integer `r >= 1`. The constants and the threshold in k may depend on all these parameters. Nothing in these estimates gives a bound uniform over all p > 0 or over r growing with k.

## Exact statement mapping

| Final-draft statement | Verified spectral Lean declaration | Remainder |
|---|---|---|
| Unprocessed single-output entropy (r = 1) | `AppendixB.single_output_r1`, `single_output_r1_infimum`, `single_output_r1_minimum` | O(k^(-5/2)) |
| Antisymmetric single-output entropy | `AppendixB.single_output`, `single_output_infimum`, `single_output_minimum` | O(k^(-5/2)) |
| Unprocessed Bell entropy (r = 1) | `AppendixB.bell_output_r1` | O(k^(-4)) |
| Antisymmetric Bell entropy | `AppendixB.bell_output` | O(k^(-3)) |

The theorems quantify over every admissible fixed real parameter, including p = 1 through the Shannon branch. Their bounds are eventual inequalities, not deductions from sampled numerics. `Entropy/Minimum.lean` extends the development with compactness and eventual attained minima. It compiles cleanly; `MinimumAudit.lean` audits all 12 new declarations, whose only axioms are `propext`, `Classical.choice`, and `Quot.sound`. The logs are `validation/Minimum.log` and `validation/MinimumAudit.log`.

The Lean spectra are `shuffle k r q` and the weighted list `dm k j, bellNu k r t j`. These agree mathematically with the operator spectra established in the paper, but the Lean code does not construct the tensor antisymmetrizer, the channel, or the partial-trace maps. Therefore it is not a full Lean verification of the random-channel theorem. Operator identifications are proved in the manuscript and independently checked in finite dimensions by Python. A theorem defined directly on `bellNu` must not be described as a formalization of that missing operator identification.

## Single-output proof

The compactness step controlling each coordinate from `c_t(u_i) <= 1/k` is uniform over the body. The subsequent estimates imply `sum x_i^2 = O(1/k)` and `abs(mean x) = O(1/k)` by Cauchy–Schwarz. Dividing by `t + mean x` is legitimate for sufficiently large k.

The cosine witness is valid for k >= 3. Its constraint has leading value `(1-k^(-1/2))^2/k`, while the summed cubic remainder is O(k^(-2)); the slack is of order k^(-3/2), which dominates this remainder. Its variance has the stated leading constant. The Lean proof instead uses a two-spike feasible witness; both prove the same optimization statement.

The complement-counting variance identity is correct. Replacing `(k-r)/(r*k*(k-1))` by `1/(r*k)` introduces O(k^(-3)) after multiplication by the input variance O(k^(-1)). This is smaller than the claimed O(k^(-5/2)) remainder. The entropy remainder is uniform over the entire body: the averaged cubic error is bounded by the maximum coordinate times the averaged second moment. The p = 1 branch gives the same coefficient.

## Antisymmetric channel and Bell spectrum

The coefficient in the one-leg channel is `k/D = r/N`. The one-body marginal is `N/r` times the identity; consequently the channel preserves trace. Since the Slater basis is real, the conjugate-channel and vectorization conventions used in the Bell calculation are consistent.

The exact identities are

- `sum_ab L_ab Y L_ba = r^2 R_r* R_r(Y)`;
- `R_l R_l* = ((k-2l+2) id + (l-1)^2 R_(l-1)* R_(l-1))/l^2` for l >= 2;
- `R_1 R_1* = k id` on the one-dimensional zero-particle operator space.

For k >= 2r the right-hand side in the recursion is strictly positive. Thus R_l is onto; all nonzero eigenvalues transfer with their multiplicities and the remaining kernel dimension is the difference of the two operator-space dimensions. This justifies the multiplicities `d_j = choose(k,j)^2 - choose(k,j-1)^2`, with `choose(k,-1)=0`, and the eigenvalues

`w_j = (r-j)(k-r-j+1)/(k*N^2)`.

All these constants are correct. The formula is only used for k >= 2r, which is automatic eventually when r is fixed. It should not be extended as written to arbitrary r <= k: the multiplicity differences need not then be nonnegative.

For the entropy expansion, the j=r-1 eigenspace has mass `r^2/k^2+O(k^(-3))` and its rescaled eigenvalue tends to `1+gamma/r^2`. The remaining exceptional masses are O(k^(-4)); the bulk Taylor term is O(k^(-4)). All rescaled eigenvalues stay in a fixed compact positive interval for sufficiently large k. This validates the real-power Taylor estimates, including 0<p<1. The resulting coefficient is exactly `B_{p,r}(gamma)`.

## Small manuscript repairs

1. State the lift–reduce recursion for `2 <= l <= r`; give its base case `R_1 R_1* = k id` separately. As presently written, the l=1 case displays the undefined symbol R_0 multiplied by zero.
2. Add the convention `choose(k,-1)=0` when defining d_0.
3. After the recurrence, add: “Since k >= 2r, the right-hand side is strictly positive. Hence R_l is onto, and the remaining eigenvalue is zero with multiplicity d_l.” This supplies the rank point used by the induction.
4. End the opening paragraph of the entropy appendix with a period. No coefficient or remainder change is needed.

## Executed Python checks

`verify_entropy.py --output final_entropy_results.json` passed all checks: 54 exact subset cases, 900 exact multiplicity/trace cases, 3600 high-precision power-remainder samples, localization/body samples, four independent exterior-matrix cases, and the asymptotic grids. Decimal arithmetic uses 90 digits and is not interval arithmetic; the one-copy grids evaluate a feasible witness, not a global numerical optimizer.

`verify_tensor_spectra.py` adds a separate construction from signed permutation tensors. In nine pairs `(k,r) = (2,1),(2,2),(3,2),(3,3),(4,2),(4,3),(4,4),(5,2),(6,3)` it exactly checks integer versions of the one-leg map and ordinary partial trace against the exterior formulas. It also exactly checks the twirl identity. Bell eigenvalue comparisons are made only when k >= 2r; the largest floating residual is below 5e-17. These finite checks are not universal proofs.

The attached `AppendixB(1).lean` is byte-identical to the original source repaired in the previous verification: SHA256 `b64174a91841509476e71c2d3973ded35b1d0ef8f3212bb3af559262b4c9771e`. The attached `verify_appendixB(1).py` exits successfully but only prints many results. Its float64 Taylor calculation prints a spurious ratio about 6.26e31 from catastrophic cancellation; its separate high-precision value is 0.230501. Use the assertion-based replacement for reproducible regression checks.
