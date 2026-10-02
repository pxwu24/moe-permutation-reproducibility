# Entropy appendix mathematical review

All four stated entropy estimates are correct, conditional on the output-body and channel-spectrum identifications used in the appendix. The scalar arguments contain no substantive gap. The operator audit independently found the antisymmetric spectrum derivation correct.

## Results checked

1. Single output: `log(k) - 2 p (1-t)/(t k^2) + O(k^(-5/2))`.
2. Single output after fixed-r antisymmetric postprocessing: `log choose(k,r) - 2 p (1-t)/(t r k^2) + O(k^(-5/2))`.
3. Bell output: `2 log(k) - A_p(t)/k^2 + O(k^(-4))`.
4. Bell output after fixed-r antisymmetric postprocessing: `2 log choose(k,r) - B_{p,r}((1-t)/t)/k^2 + O(k^(-3))`.

All statements include p=1 and every fixed real p>0. Constants are not uniform as p approaches 1, as t approaches either endpoint, or as r varies; the paper does not assert such uniformity.

## Exact entropy identity and Taylor estimates

For p≠1, `1+X=M^(p-1) sum_j d_j nu_j^p>0`; for p=1, `X>=0` follows from `(1+y) log(1+y)-y>=0`. Thus F_p(X) is inside its stated domain. This useful domain sentence was missing but follows immediately from the existing assumptions.

The explicit cubic constant `8p^3+3p^2+2p` is valid: let L=log(1+y), use |L|≤2|y|, |L-y|≤2y², the cubic logarithm remainder≤2|y|³, and the cubic exponential remainder≤|pL|³. These respectively contribute 8p³, 3p², 2p. The p=1 constant 4 is also valid. The proposition uses one C_p for both local estimates; the separate constants displayed in its proof should be replaced by their maximum if one common constant is intended. This is a notation repair, not a theorem change.

The uniform estimate follows with Q≤eta² and |X-kappa_p Q|≤C eta Q. No dimension-dependent constant appears.

## Localization and two-spike witness

The cost inequality is correct. In the proof, the bound ||w||₂≤2/sqrt(k) follows directly from the displayed cost inequality and sum c_i≤1/k, not merely the coordinate estimate |w_i|≤2/sqrt(k). Making that implication explicit prevents a reader from incorrectly summing the coordinate estimate.

For the two-spike witness, the conditions sigma²≤min(t,1-t) ensure that both claimed square roots are nonnegative, so c_t(u_±)=sigma² is exact. Its exact centered squared numerator is

`4 t(1-t)/k + ((1-2t)^2/2 - 2t(1-t))/k^2 - (1-2t)^2/k^3`.

The normalization denominator is `(t+(1-2t)/k²)²`. Hence the witness gives `||epsilon*||²=4(1-t)/(t k)+O_t(k^-2)`, stronger than the stated lower bound. This validates the sharp constant in the single-output estimates.

## Bell estimates

The m=r block contributes O(k^-4), the m=r-1 block contributes `r² psi_p(gamma/r²)/k²+O(k^-3)`, and all m≤r-2 blocks together contribute O(k^-4), since r is fixed. For r=1, the multiplicity weight is exactly 1/k² and y_0=gamma+O(k^-2), giving O(k^-4). The passage through F_p adds only O(k^-4), so the claimed remainders follow. A single uniform Taylor expansion in all Bell y_m would be invalid because the exceptional y_m do not tend to zero; the supplied proof correctly uses compact-interval Lipschitz bounds for those blocks.

High-precision spot checks independently supported these remainder orders. They are numerical evidence, not proof. Examples: for p=1,t=.27,r=1, k^4 times the residual at k=100,200,400,800 was approximately -7.195978,-7.195287,-7.195114,-7.195071. For p=.7,t=.27,r=2, k^3 times the residual was .793246,.798797,.801643,.803084.

## Original Python coverage

The attached verify_appendixB.py checks scalar samples and combinatorial identities; it does not compute any of the four entropy asymptotics. Most conditions only print values without asserting them. The float64 cubic remainder test can suffer cancellation near zero. It should be presented as exploratory numerical checking, not a certificate. Exact integer identities, high-precision entropy calculations, explicit assertions, and operator spectral checks improve its coverage; none replaces the mathematical or Lean proofs.
