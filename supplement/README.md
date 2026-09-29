# Main-theorem proof

[`main_theorem.tex`](main_theorem.tex) contains the main-theorem proof and its
parameter table. It defines the finite-field Pauli postprocessing and
classical Pauli-label extension, derives the one-copy and Bell-output entropy
bounds, and gives the explicit choice `r_N = 10^11 ceil(N)` and the input/output
dimension estimates.

[`main_theorem_preview.pdf`](main_theorem_preview.pdf) is a three-page
standalone preview. Its [wrapper](main_theorem_preview.tex) supplies illustrative
counters and labels for statements outside the preview. The fragment uses
standard LaTeX with `amsmath`, `amssymb`, and `booktabs`.

To verify the mathematical results, run from the repository root:

```sh
bash lean/verify-all.sh
```

The [Lean verification guide](../lean/README.md) maps each supplemental result
to its source file and theorem name and explains how to inspect individual
statements. [Formalization notes](PROOF_NOTES.md) describe the channel
construction and representation conventions.
