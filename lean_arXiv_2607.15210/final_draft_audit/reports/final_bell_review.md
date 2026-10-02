# Bell-output verification against the final draft

Source: final draft uploaded 2026-10-02, lines 945–1076 and 1978–2139.

## Mathematical conclusion

The Bell-output limit, its two limiting eigenvalues, the second Choi moment,
and the fixed-k entropy corollary are correct, conditional on the stated
strong block-modification theorem including normalized-trace convergence.
The large-k Bell entropy expansion is also correct and is independently
covered by the existing compiled entropy modules.

The final draft's scalar log-determinant proof is preferable to the earlier
joint-strong-limit proof: it obtains the required mixed moments from scalar
laws and a uniform finite-difference bound. No unjustified interchange of a
pointwise limit and a derivative is needed.

## Detailed checks

1. Choi indices are correct. The conjugate-channel contraction is
   `(1/n) sum_ab J[(a,i),(b,j)] conjugate(J[(a,p),(b,q)])`.
   Hermiticity turns it into `(1/n) Tr(J_ij J_qp)`.
2. If `X > 0`, positivity of `T_n` gives
   `T_n(X) >= lambda_min(X) P_A,n`. Together with the compression lower edge,
   this places spectra uniformly away from zero. Strong convergence plus
   normalized-trace convergence then permits the logarithm.
3. The logarithmic potential has the stated sign and additive constant.
   Differentiating it in `z<0` gives `G(z)`; both it and the log moment differ
   from `log(-z)` by a quantity tending to zero at negative infinity.
4. The negative branch can be justified explicitly. Set
   `Phi_X(w)=1+k sum_i g_t(a_i w/k)`. For `w<0`, it is strictly increasing,
   with limits `1-k^2 t<0` at negative infinity and `1` at zero. Its unique
   root is `w_X`. On `(w_X,0)`,
   `K_X'(w)=(w Phi_X'(w)-Phi_X(w))/w^2<0`, so the inverse branch continues
   from negative infinity to zero without a turning point. This supplies
   the details behind the draft's brief continuation sentence.
5. At the identity, the root is
   `y_0=-(k^2-1)/(k^2(k^2 t-1))`, and `g_t(y_0)=-1/k^2`.
6. For a traceless direction, the first root variation vanishes. Stationarity
   of the potential in `w` removes its second root variation. This gives
   `c1=-k y_0^2 R_t'(y_0)=-k(1-t)/(k^4 t-2k^2 t+1)`.
   Homogeneity and the vanishing traceless first variation give
   `c0=(-1-k c1)/k^2`; in particular, no scalar–traceless cross term was lost.
7. The positive unital map `C_n` is contractive on Hermitian matrices. The
   central difference bound in the draft holds; the scalar calculation even
   gives constant 2 in place of 4.
8. To make the almost-sure event explicit, choose a finite Hermitian basis,
   its pairwise sums, and a countable sequence of nonzero steps tending to
   zero. Scalar convergence at these finitely/countably many points and the
   uniform central difference estimate yield all mixed moments on one event.
9. Complexification uses `C_n(E_ji)=J_ij`. The second invariant bilinear form
   contributes `delta_ip delta_jq`, exactly as stated. The coefficients obey
   `-c0=beta`, `-c1=r/k`, and `-c0-k c1=alpha`.
10. Since output dimension k is fixed, entrywise convergence yields norm
    convergence. Fixed-dimension Renyi continuity holds for each finite p>0.
    The rank-entropy endpoint p=0 is not covered by this continuity argument.

## New Lean verification

All modules use Lean 4.19.0 and the existing pinned mathlib environment.
No new axioms or `sorry` are introduced. Exact checked declarations:

- `Entropy/BellLimitTransfer.lean` (3): deterministic uniform-approximation
  transfer, fixed-step central-difference convergence, and countable-step
  transfer to second-moment convergence.
- `Entropy/BellLimitCoefficients.lean` (8): denominator identity/positivity,
  `0<r<1`, Hessian/Bell coefficient identities, spectrum normalization and
  positivity, negative-root arithmetic, Bernoulli derivative substitution.
- `Entropy/BellFiniteDifference.lean` (3): symmetric logarithmic remainder,
  divided central remainder, and normalized weighted spectral remainder.
- `Entropy/BellMatrixIdentities.lean` (3): Hermitian Choi block-entry
  contraction, trace-square decomposition, and overlap/purity contraction.

**Scope boundary:** these modules do not yet formalize the identification of
`mu_X` as a free-convolution probability law, the analytic log-potential
identity for that measure, the full quantum-channel tensor framework, or the
almost-sure strong-convergence input. The limit-transfer theorem exposes its
pointwise convergence and derivative hypotheses; the coefficient module
proves actual rational identities rather than assuming their conclusions.
Thus the stochastic Bell-limit theorem is mathematically audited but is not
an end-to-end Lean theorem in the current development. The separate Bell
entropy modules prove asymptotics of the explicitly defined spectra.

## Python checks

`final_bell/verify_bell_limit.py` passes with assertions enabled. It checks:

- Five independent finite random projection examples: Choi contraction,
  normalization, overlap/purity, contractivity, determinant identity, and
  the central-difference bound. Largest entry-identity discrepancy is below
  6e-17 and largest overlap/purity discrepancy below 1.2e-16.
- Six `(k,t)` pairs, including parameters close to the local-support
  threshold, with 75-digit scalar arithmetic. Three directions per pair
  test the full Hessian, traceless Hessian, and scaling direction. The
  largest finite-difference Hessian discrepancy is below 7e-25.

These are numerical cross-checks, not interval certificates of a universal
asymptotic theorem. The exact scalar identities and remainder bounds are
also checked by Lean as listed above.
