# Verification of the entropy appendix

The mathematical audit found all four entropy estimates correct, with the output-body and channel-spectrum identifications used in the paper. The revised appendix clarifies several intermediate steps; it does not change the leading coefficients or remainder orders. See [mathematical_review.md](mathematical_review.md) for the detailed audit and [entropy_revised.tex](entropy_revised.tex) for the revised text.

Throughout, $t\in(0,1)$, $p>0$, and the positive integer $r$ are fixed as $k\to\infty$. Write $\gamma=(1-t)/t$ and $D=\binom{k}{r}$. The estimates checked are:

| Quantity | Leading expansion | Remainder |
|---|---|---|
| Minimum single-output entropy | $\log k-2p\gamma/k^2$ | $O_{p,t}(k^{-5/2})$ |
| Minimum single-output entropy after antisymmetric postprocessing | $\log D-2p\gamma/(rk^2)$ | $O_{p,r,t}(k^{-5/2})$ |
| Bell-output entropy | $2\log k-A_p(t)/k^2$ | $O_{p,t}(k^{-4})$ |
| Bell-output entropy after antisymmetric postprocessing | $2\log D-B_{p,r}(\gamma)/k^2$ | $O_{p,r,t}(k^{-3})$ |

These statements include $p=1$. Their constants are allowed to depend on the fixed parameters; the appendix does not claim uniformity as $p,t,r$ vary.

## Mathematical changes

- The exact entropy expansion now explicitly checks that its argument lies in the domain of $F_p$.
- The local Taylor bounds may use a common constant by taking the maximum of their separate constants.
- The localization proof makes the summed squared bound explicit before bounding the mean displacement.
- The two-spike witness has the claimed exact costs, and its squared normalized displacement is $4\gamma/k+O_t(k^{-2})$. Together with the uniform lower bound, it supplies the sharp single-output coefficient.
- The Bell proof uses compact-interval bounds on the exceptional spectral blocks. Those perturbations need not tend to zero, so a Taylor expansion at zero cannot be applied uniformly to every Bell block.
- The antisymmetric reduction, lifting, twirl, and spectral identities were independently reviewed. Their finite-dimensional matrix checks are described below.

## Python checks

Install the listed dependencies and run:

```bash
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 python verify_entropy.py --output python_results.json
```

The environment variable is optional; it limits NumPy's numerical-library threads. The script uses a fixed random seed, explicit assertions, and the standard-library `decimal` module at 90 digits. It does not require `mpmath`. A failed assertion stops the run instead of writing a successful result.

The saved [python_results.json](python_results.json) records a successful run with Python and NumPy version information and these checks:

| Check | Coverage | Arithmetic |
|---|---|---|
| Subset mean and quadratic identities | 54 tested $(k,r)$ pairs | Exact integers and `Fraction` |
| Multiplicity sums, trace normalization, spectral recursion | 900 tested $(k,r)$ pairs | Exact integers and `Fraction` |
| Explicit cubic power remainder | 3,600 samples | 90-digit `Decimal` |
| Logarithmic remainders and exact entropy identity | Includes $p=1$ and $p$ near 1 | 90-digit `Decimal` |
| Scalar localization inequality | 20,000 samples | NumPy floating point |
| Feasible-body localization | 144 sampled vectors | NumPy floating point |
| Exterior-power operator identities and spectra | $(k,r)=(2,1),(4,2),(5,2),(6,3)$ | NumPy floating point |
| All four entropy expansions | 36 $(p,t,r)$ triples and five dimensions $k=100,200,400,800,1600$ | 90-digit `Decimal` |

The largest sampled ratio in the cubic power bound is approximately `0.2305010931`, below its required upper bound of 1. The independently evaluated exact entropy identity has maximum absolute error below `1.8e-82`. Operator spectral errors are below `2.3e-16` in the tested cases.

The operator tests construct exterior annihilation matrices, the actual reduction superoperator, and the collective one-body operators. They check the lift–reduce recurrence, one-body twirl, postprocessed Bell spectrum, and shuffled spectrum of a non-diagonal density matrix. This exercises the operator construction independently of merely substituting the claimed spectral formula into itself.

The asymptotic records contain the scaled deficits and residuals. The single-output computations use the explicit feasible two-spike witness and group subsets according to their two exceptional coordinates. They do **not** numerically optimize the whole output body or certify its global minimum. The Bell computations use the full spectrum with exact integer multiplicities. Residuals are scaled by $k^{5/2}$ for the single witness, by $k^4$ for the unprocessed Bell state, and by $k^3$ for the postprocessed Bell state.

### What these Python results establish

The integer and rational calculations are exact **for the tested parameters**. Decimal calculations provide high-precision checks, but they are not directed-rounding interval certificates. Floating-point calculations are numerical checks with explicit tolerances. No finite collection of these tests proves a universal identity, an asymptotic statement, or global entropy minimization. The universal arguments belong to the mathematical proof and to the Lean statements actually compiled and audited.

The original attached Python file mainly printed diagnostic values and did not directly evaluate the four entropy asymptotics. Its floating-point cubic remainder test printed a very large ratio while exiting successfully, due to cancellation near zero. Its high-precision counterpart was consistent with the bound. The revised script removes that misleading floating-point remainder calculation and adds assertions and direct entropy checks.

## Lean verification

**STATUS: VERIFIED for all four spectral entropy estimates, including p=1.**

The revised modular development and the standalone `AppendixB_verified.lean` compile with Lean **4.19.0**, using mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All **54 original public theorem statements are preserved**. The original standalone audit covers **60 public declarations**, including infimum wrappers, and reports only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or added mathematical axiom is used.

In a fresh copy of the supplied project:

```bash
lake update
lake exe cache get
./verify_lean.sh
```

Alternatively, compile the standalone file in a project using the same pinned mathlib:

```bash
lake env lean AppendixB_verified.lean
```

`make_standalone.py` regenerates that convenience file from the maintained modular source. The final compiler output and axiom reports are in `validation/`; `verify_statements.py` checks preservation of the original theorem statements. The original, uncompiled attachment is retained only as `audit_original/AppendixB_original.lean` for comparison, together with its failure log.

The two single-output estimates include uniform lower bounds over the whole explicit eigenvalue body, a feasible matching witness, and bounds for the actual infimum. The added `Entropy/Minimum.lean` now proves compactness and eventual attainment, with `single_output_minimum` and `single_output_r1_minimum` giving the optimized error bounds directly. The two Bell results prove the entropy expansions for the exact explicit spectra.

**Scope of this subdirectory:** the scalar spectral estimates and their intermediate analytic, combinatorial, and localization results. The parent project additionally contains the actual channel constructions, spectral identifications, random limits, and matrix-entropy bridges. Use [the current numbered result index](../README.md) for the complete proofs and all related files. The older `LEAN_SCOPE.md` records the earlier standalone export.

## Files

- `entropy_revised.tex`: revised appendix.
- `mathematical_review.md`: mathematical findings and scope.
- `verify_entropy.py`: assertion-based exact and numerical checks.
- `python_results.json`: reproducible results and complete asymptotic tables.
- `requirements.txt`: pinned Python dependency used for the saved run.
- `AppendixB_verified.lean`: standalone checked Lean development.
- `AppendixB.lean`, `Entropy.lean`, and `Entropy/*.lean`: modular checked development.
- `Audit.lean`: Lean axiom-audit commands.

## Final-draft extensions

The modular aggregate additionally includes minimum attainment, concrete support-body geometry, deterministic limit transfer, Bell finite-matrix identities and a universal all-positive-order spectral nonadditivity theorem. `AuditAll.lean` checks all modular theorem declarations, including generated/private helpers. The original standalone export remains an export of the entropy estimates and infimum wrappers. See [the current numbered index](../README.md) for the operator/free-probability proofs and combined reproducible build; the older seven-part audit is retained as a historical record.
