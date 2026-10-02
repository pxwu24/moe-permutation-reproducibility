# Final-draft verification — 2026-10-02

The mathematical audit supports the seven requested results, using the stated
strong block-modification theorem as the permitted external input, after the
clarifications below. **The complete paper is not yet formalized in Lean.**
In particular, the existing scalar support duality is not a proof identifying
the right spectral edge of the actual free-convolution measure.

## Seven-part coverage

| Step | Mathematical audit | Kernel-checked Lean coverage | Remaining Lean work |
|---|---|---|---|
| 1. Random compression | Correct, including arbitrary signs and infinite-parameter/atomic endpoints | Matrix block identity; Bernoulli projection convergence; full scalar max/inf duality; finite/infinite critical-point classification; actual Cauchy-transform continuation obstruction; common almost-sure event from fixed-parameter convergence | Free-convolution/R-transform identification and its actual inverse branch; connect it to the permitted strong-convergence input |
| 2. One-copy entropy | Correct; the proved error is O(k^(-5/2)) | Actual normalized spectral body, uniform entropy expansion, sharp witness, and eventual attained minimum | Matrix output-body/Hausdorff identification and its quantum-channel instantiation |
| 3. Antisymmetric one-copy entropy | Correct for fixed r | Exact subset variance and entropy of the shuffled spectra, with an attained minimum and O(k^(-5/2)) remainder | Construct the antisymmetric channel and prove its operator-to-spectrum identification |
| 4. Bell entropy | Correct; O(k^(-4)) for r=1 | Explicit Bell spectrum entropy; actual finite block contractions/overlap identity; rational coefficients; logarithmic finite-difference bound and convergence transfer | Free-law logarithmic potential and Hessian as actual measure integrals; full stochastic channel-limit instantiation |
| 5. Postprocessed Bell entropy | Correct; O(k^(-3)) for fixed r | Exact multiplicity/trace formulas and entropy of the weighted Bell spectrum | Universal operator proof of the lift–reduce spectrum and the channel tensor construction |
| 6. Nonadditivity for every p>0 | Correct **for each fixed p**, with dimensions depending on p | Unconditional positive coefficient gap and eventual strict violation for the explicit limiting spectra; finite-index transfer lemma with explicit limit hypotheses | Construct actual channels and discharge the probabilistic/operator bridges above |
| 7. Output dimension 182 | Correct: k_high(1) <= 182 and limiting gap >477/10^6 | Global scalar eigenvalue bound, real-logarithm certificate, numerical shape hypotheses, generic negative-curvature obstruction; entropy comparison conditional on one-high minimizer shape | Boundary perturbation, multiplier/constraint-surface argument, and hence the full minimizer-shape theorem |

The distinctions in the last column remain even though every uploaded proved
Lean theorem passes an axiom audit. A theorem may be kernel-correct while
still requiring hypotheses that are not discharged for the paper's operators.
No additional mathematical axiom or `sorry` is used to conceal those gaps.

## Necessary manuscript corrections

1. **Quantifiers in the abstract.** Replace the claim that one channel pair
   works simultaneously for every p>0 by the theorem actually proved:
   for each p>0 there exists a channel pair. The fixed choices r=5 and gamma=375
   do not make the chosen dimensions independent of p.
2. **Verification declaration.** Replace “Lean verification of all the
   mathematical proofs” with a description of partial formalization and a
   reference to this coverage report.
3. **Compression statement.** Introduce a sequence P_n,d_n with fixed k;
   its present opening introduces only one P,n,d.
4. **Choi ordering.** The preliminary convention gives J_phi=A tensor I.
   Explicitly switch to the output-first convention C_phi=I tensor A when
   invoking the block theorem. The appendix already makes this distinction.
5. **Positive normalization mass.** Define the currently undefined
   m_(k,t)=min_{u in D_(k,t)} sum_i u_i>0. Compactness and k^2 t>1 prove it.
6. **Hausdorff lemma.** Require nonempty compact convex sets.
7. **Lift–reduce induction.** State the recurrence for ell>=2, give its
   ell=1 base separately, define choose(k,-1)=0, and explain surjectivity
   from positivity for k>=2r.
8. **Multiplier notation.** In the second variation, hold mu/s(u_*) fixed at
   the minimizer u_*; do not differentiate s(u) inside the multiplier.

`corrections.tex`, `output_space_repairs.tex`,
`antisymmetric_spectrum_repairs.tex`, and `main_result_verified.tex` provide
short replacement passages. No leading entropy coefficient needs changing.
The title's p=0 case is a separately cited known result, not a consequence
of the new positive-p construction; make that distinction explicit if keeping
p>=0 in the title. Update the stale PDF metadata. The attached source also
omits its final `\end{document}` and does not include `min.bib`; this audit
does not claim a successful full-manuscript LaTeX build.

## Executed verification

The fresh combined build compiled **69 modules** and audited **697 theorem
declarations, including generated/private helpers**. Only `propext`,
`Classical.choice`, and `Quot.sound` occur in their transitive axiom closures;
no project logical axioms occur. The 54 original public statements are
preserved. All seven Python runs passed. These counts do not change the
formalization boundaries above. See [the complete theorem map](THEOREM_MAP.md),
[Lean build record](lean_verification.json), [Python run record](python_verification.json),
and [summary](verification_summary.json).

## Formal sources

The existing root project contains the preliminary, Gaussian/Haar, scalar
compression, and k182 results. Newly added root modules are
`CompressionEndpointGlue.lean`, `K182ShapeCalculus.lean`, and
`K182SecondVariation.lean`, `OutputSpaceMatrix.lean`, and
`OutputSpaceCompressionBridge.lean`. The last module proves the normalized
compression limit for actual growing matrices, with the random compression
limit as its spectral input. See their audits and the individual reports.

The self-contained [`../entropy`](../entropy) project contains the repaired
54 original public theorem statements unchanged, the infimum wrappers, and
the new minimum-attainment, output-space, Bell, and main-result results.
Its central conclusions are:

- `AppendixB.single_output_minimum` and `single_output_r1_minimum`;
- `AppendixB.bell_output` and `bell_output_r1`;
- `AppendixB.main_coefficient_gap` and `main_coefficient_strict`;
- `AppendixB.spectral_nonadditivity_all_orders`;
- `OutputSpaceVerification.concrete_normalized_support_tendsto`.

`UnprovedTargets.lean` is explicitly a statement-only file. Compiling it
does not prove the random-compression theorem. The older
`AppendixB_verified.lean` standalone export covers the entropy estimates and
infimum wrappers; use the modular `Entropy.lean` aggregate for the additional
results in this audit.

## Python checks and certification

| Script | Purpose | Kind of evidence |
|---|---|---|
| `random_compression_check.py` | Arbitrary-sign duality, endpoint cases, finite Haar matrices | High-precision diagnostics; not a stochastic convergence proof |
| `../entropy/verify_entropy.py` | All four entropy formulas, exact subset/trace identities, asymptotic grids | Exact finite identities plus numerical diagnostics; no claim that witness sampling optimizes globally |
| `../entropy/verify_tensor_spectra.py` | Independent signed-permutation tensor/Slater construction | Exact integer identities in nine tested dimensions plus numerical eigenvalues |
| `verify_bell_limit.py` | Finite Choi/Bell identities and scalar Hessians | Finite matrix and 75-digit diagnostics |
| `verify_main_coefficient.py` | Closed coefficient versus integral, including p near 1 | 100-digit diagnostics; the all-real-p inequality is proved in Lean |
| `certify_k182_exact.py` | All numerical inequalities in the k182 certificate | Exact rational interval certificate, Python standard library only |

The exact rational interval for the scalar lower bound
`2 h_182(162513/10^6) - S_1(Bell)` is contained in

    (0.00047756110230383259375495,
     0.00047756110230383259375496).

This is a certified lower bound for the optimized entropy gap, using the
mathematically proved minimizer-shape lemma. It neither proves the minimality
of 182 nor supplies an explicit finite input dimension n. The attached
mpmath script compared interval endpoints with default-precision `mpf`
thresholds; the replacement compares exact rationals and uses a proved
logarithm-series remainder.

The supplied original entropy smoke script exits successfully despite a
catastrophically cancelled float64 remainder ratio. Use the replacement
assertion-based high-precision scripts; they reject execution with disabled
assertions where relevant. The exact rational k182 script uses explicit
checks and also works under `python -O`.

## Reproduction

From `lean_arXiv_2607.15210`, with Lean 4.19.0 and Python installed:

```sh
lake update
lake exe cache get
bash verify_final.sh
```

`verify_final.sh` checks both Lean projects and runs all Python checks after
installing the listed Python dependencies separately. First run
`python -m pip install -r final_draft_audit/requirements.txt` if needed.
The combined root build exposes the entropy library automatically. The entropy
subproject can also be checked independently after its own `lake update` and
`lake exe cache get`. The scripts do not install dependencies implicitly. See `verification_summary.json` and the build/audit
logs for the executed verification evidence.

## External inputs checked

- Nechita, [arXiv:1802.00067v2, Section 5](https://arxiv.org/pdf/1802.00067):
  Definition 5.1 uses the output-first Choi convention; the strong theorem
  is Theorem 5.2. Correct the appendix's “Theorem 5.1” citation for the condition.
- Belinschi–Collins–Nechita,
  [arXiv:1305.1567](https://arxiv.org/abs/1305.1567): the cited 183 threshold
  concerns their random-channel/Bell criterion. The comparison must remain
  ensemble-specific.

`source_provenance.json` identifies the exact attachments and base repository
commit. The full manuscript is not published by this code upload.
