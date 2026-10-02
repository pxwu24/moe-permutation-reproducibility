# Operator spectral audit

Reviewed the operator arguments in the supplied entropy appendix (the four propositions preceding the Bell entropy proof). The stated formulas are correct under the standing assumptions `r ≥ 1` and `k ≥ 2r`. No correction to their constants or multiplicities is required.

## Antisymmetrizer and reduction

The coset decomposition of the permutation group gives

`Π_m = (I − Σ_{j<m} F_{jm})(Π_{m−1} ⊗ I)/m`.

Taking adjoints gives the second displayed factorization. The ordinary, unnormalized partial trace maps operators supported on `Λ^m C^k` to operators supported on `Λ^(m−1) C^k`. Its Hilbert–Schmidt adjoint is exactly the compressed lift in the manuscript. In particular, `R_1 R_1* = k`, with no missing dimension factor.

## Twirl and lift–reduce identity

The manuscript's crossed-swap calculation is valid. In the lift–reduce proof, the potentially delicate identity follows from

`F_lm = F_jl F_jm F_jl` and `(Z ⊗ I)F_jl = −(Z ⊗ I)`.

It gives `F_jm (Z ⊗ I) F_lm = −F_jm (Z ⊗ I) F_jm F_jl`; compression changes the remaining minus sign back to plus. There are precisely `(m−1)^2` double-swap terms. Thus

`H_m = ((k − 2m + 2) id + (m−1)^2 G_(m−1))/m^2`

is correctly normalized.

An independent exterior-algebra check uses annihilation maps `a_b : Λ^m → Λ^(m−1)`. In normalized Slater bases,

`R_m(Y) = (1/m) Σ_b a_b Y a_b*`, and `L_ab = a_a* a_b`.

Therefore `Σ_ab L_ab Y L_ba = m^2 R_m* R_m(Y)` directly. This could shorten the twirl proof, but the existing proof avoids additional notation and is already sound.

## Eigenvalues and the Bell state

The induction transfers the positive eigenvalues of `H_r` to `G_r` with multiplicities. For `k ≥ 2r`, all displayed eigenvalues with `m < r` are positive; their successive differences are `(k − 2m)/r^2 > 0`. Thus the stated multiplicities refer to distinct eigenvalues. The kernel dimension is the telescoping dimension difference in the manuscript.

The vectorization convention is consistent: `(X ⊗ Y) vec(Z) = vec(X Z Y^T)`. Since the collective one-body matrices are real and `L_ab^T = L_ba`, the Bell output is unitarily equivalent to `r^2 G_r/(k N^2)`. Hence

`w_m = (r−m)(k−r−m+1)/(k N^2)`

with multiplicity `choose(k,m)^2 − choose(k,m−1)^2` is correct, and the spectrum has trace one.

## Independent numerical checks

Constructed signed exterior annihilation matrices directly, then formed `R_m` as a matrix on the Hilbert–Schmidt operator spaces. Checked `(k,r) = (2,1), (4,2), (5,2), (6,3)`.

| Check | Largest absolute residual |
|---|---:|
| Lift–reduce matrix identity | 0 at float64 precision |
| Twirl matrix identity | 0 at float64 precision |
| Full `G_r` spectrum, including multiplicities | 1.50e−15 |
| Bell trace normalization | 1.12e−16 |

These are independent finite-dimensional consistency tests, not proofs for all dimensions.

## Lean coverage limitation

The supplied `AppendixB.lean` explicitly defines `bellNu` to be the proposed scalar eigenvalue formula. The lemmas `eig_recursion`, `mult_sum`, and `trace_identity` check its arithmetic and normalization. They do not construct antisymmetric tensor powers, partial traces, `R_m`, `G_m`, the postprocessing channel, or the actual Bell-output operator. The revised development now compiles, and its Bell asymptotic theorem is a theorem about this explicitly defined weighted spectrum. It does not formalize the operator-to-spectrum identification proved above. The final verification report should retain this distinction.

## Minimal editorial changes

1. Keep the four operator propositions and their proofs; no mathematical correction is necessary.
2. State `1 ≤ r` explicitly when the spectrum propositions are extracted from the appendix context.
3. Optionally add one sentence saying that positivity of `H_r` gives its full rank, so the remaining multiplicity of `G_r` is its kernel dimension.
4. Use `equation` or `align` environments in place of unnumbered display delimiters, as requested by the user.
