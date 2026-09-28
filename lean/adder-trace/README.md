# Modular-adder trace estimates

`AdderTrace.lean` is the complete, previously verified source for the actual
two-register adder construction. Its theorem
`AdderTrace.technical_trace_bound` is Proposition 4 of the Supplement, with
only the parameter hypotheses printed in the paper. The Gaussian-integer
grid and the filter are the actual full definitions, not abstract quantities
assumed to satisfy moment or counting estimates.

`SupplementAdder.lean` presents the word-trace and matrix-moment estimates
using the statements of Lemmas 5 and 6. It imports the complete proof above.

```sh
bash verify.sh
```

Dependencies: Lean 4.24.0 and mathlib
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The supplied Lake manifest pins
transitive dependencies. No Physlib dependency is needed by this project.

The matrix trace is written using its real part in ordered inequalities;
`AdderTrace.prescribedFilter_trace_real` identifies it with the actual trace.
Matrix rows and columns are labeled by tuples of residue pairs, which is
precisely the computational basis of the two-register tensor construction.

The historical `verification/verification.log` and
`verification/verification_status.json` belong to the unchanged
`AdderTrace.lean` source. Fresh checks of the project and the paper-statement
wrappers write separate `current-*` records. `Audit.lean` rejects any dependency
on a placeholder or a nonstandard axiom.

The formal proof of Lemma 6 uses finitely supported reduced-word convolution.
It establishes the paper's inequality but does not formalize the paper's
particular presentation using compressed finite matrices.
