# Main-theorem proof for the Supplement

Replace the existing main-theorem proof subsection (including its parameter
table) with [`main_theorem.tex`](main_theorem.tex). It uses standard LaTeX plus
`amsmath`, `amssymb`, and `booktabs`. All logarithms follow the manuscript's
convention: natural logarithms except `log_2`.

[`main_theorem_preview.pdf`](main_theorem_preview.pdf) is a standalone,
three-page preview. The wrapper `main_theorem_preview.tex` supplies illustrative
equation and table counters; do not paste that wrapper into the manuscript.

The proof keeps the proposed constants and the choice
`r_N = 10^11 ceil(N)`. It supplies the reality argument for the basic channel
and defines the Pauli-label extension explicitly. A direct Bell-state ensemble
is enough for the two-copy bound, so no minimum-entropy optimizer is needed.
Proposition numbers match the supplied 19-page manuscript: the uniform bound
is Proposition 2 and the adder trace bound is Proposition 3.

The complete Lean project is in [`../lean/entropy`](../lean/entropy/), with
`AllProofs.lean` as its entry point. Run `bash lean/verify-all.sh` from the
repository root. See [`../lean/COVERAGE.md`](../lean/COVERAGE.md) for individual
endpoints and [`PROOF_NOTES.md`](PROOF_NOTES.md) for the formalization scope.
