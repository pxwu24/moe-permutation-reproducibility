> Historical scope/report. The current numbered results and complete Lean dependencies are listed in [the project README](../README.md). Statements below about missing proofs describe the earlier snapshot.

# Theorem-by-theorem coverage

This table covers all 20 theorem/lemma/proposition/corollary environments in the attached draft. “Complete” always refers to the explicit scope in the last column; it does not turn a spectral theorem into a channel theorem.

| Label | Requested step | Lean status | Scope |
|---|---:|---|---|
| `lem:haar-projection-partial-trace` | 1 | complete | Gaussian/Haar rank theorem checked; use the explicit Gaussian proof in corrections.tex. |
| `lem:random-matrix-input` | 1 | partial | Strong block theorem is permitted externally; free-convolution R-transform and actual branch identification still unformalized. |
| `lem:bernoulli-edge-duality` | 1 | complete scalar duality; partial actual edge | Actual free-convolution measure/right edge is not connected to the formal dual. |
| `thm:output-space-limit` | 2 | partial | Actual growing normalized compression checked; density-state support, unitary transport and support-Hausdorff duality remain. |
| `cor:single-asymptotic` | 2 | complete large k spectral; partial fixed k channel | Minimum spectral asymptotics complete, channel output-set bridge partial. |
| `lem:hausdorff-support` | 2 | mathematical only | Trace/operator norm support-Hausdorff duality not formalized; add nonempty assumptions. |
| `lem:support-channel` | 2 | partial | Actual inverse-square-root matrix threshold proved; density-state maximization and channel adjoint trace identification remain. |
| `prop:eigenvalue-shuffling` | 3 | mathematical and python only | Exact subset formulas are formal; operator spectrum of antisymmetric channel is not. |
| `prop:app-antisymmetric-single-entropy-asymptotics` | 3 | complete spectral minimum | Actual attained optimization over Lam and shuffle; operator identification still external to these formal statements. |
| `thm:bell-output-limit` | 4 | partial | Actual finite contractions, coefficient algebra, remainder and transfer checked; measure logarithmic potential and stochastic channel instantiation remain. |
| `cor:joint-asymptotic` | 4 | complete large k spectral; partial fixed k channel | Explicit Bell spectrum expansion complete; product-channel minimum entropy limit bound not instantiated. |
| `lem:bell-log-hessian` | 4 | partial | Rational substitution checked; actual integral logarithmic-potential/Hessian evaluation not formalized. |
| `prop:normalized-choi-block-limit` | 4 | partial | Deterministic convergence transfer and uniform remainder proved; measure assumptions not instantiated. |
| `prop:asymptotic-choi-purity` | 4 | partial | Exact trace contractions and limiting coefficient algebra proved; stochastic moment limit remains. |
| `thm:entropy-asymptotics-antisymmetric` | 5 | complete spectral; partial channel | All asymptotics of explicit spectral lists checked; channel spectral identification missing. |
| `prop:app-antisymmetric-bell-entropy-asymptotics` | 5 | complete explicit spectrum | Weighted spectrum entropy complete; antisymmetric Bell operator identification remains mathematical/Python only. |
| `thm:main` | 6 | partial channel; complete limiting spectral | Actual channel construction and operator/probabilistic bridges are not discharged. |
| `prop:certified-k182` | 7 | complete scalar certificate; conditional global minimum | HasOneHighEntropyMinimizer remains an explicit unproved hypothesis in the Lean entropy theorem. |
| `lem:finite-k-entropy-reduction` | 7 | partial | Boundary exclusion, multiplier argument and Bernoulli feasible-curve construction/differentiation remain. |
| `lem:finite-k-scalar-certificate` | 7 | complete | Global scalar dual and all-normalized-body eigenvalue bound formalized. |
