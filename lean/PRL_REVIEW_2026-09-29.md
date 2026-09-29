# Final-supplement alignment — 29 September 2026

The supplied final subsection states the sharper asymptotic slope
`d_M(s)-2 log(1+9/M)`. The new module
[`entropy/MainSharperPostprocessing.lean`](entropy/MainSharperPostprocessing.lean)
proves this slope with explicit correction
`8 log r+4 log 108+2 log beta`, where `beta=(10001 gamma/9999)^2`.
It proves both the actual Bell-output entropy estimate and the corresponding
Holevo lower bound for the already constructed final channel.

The main theorem remains unconditional apart from `N>=1`; its channel,
`r_N=10^11 ceil(N)`, and dimension estimates have not changed.

## Written-proof corrections

- Restore the explicit finite-field Pauli randomizer and proof, as supplied
  in `supplement/main_theorem.tex`. Existence of a postprocessing map alone
  is not an explicit construction.
- State the actual Bell-output entropy bound before using that input to
  lower-bound two-copy Holevo information.
- Use the explicit `r_N` to justify the dimension growth in N.
- Before the word-trace cone argument, merge maximal equal-index runs.
  Adjacent inverse cancellation alone does not remove an interior `P^0`
  from a word such as `T_i T_i`. The existing Lean proof already handles this.
- In the moment proof's tail-space decomposition, omit zero rows and columns
  before identifying the remaining matrix with a coefficient submatrix.
- Explain reality of F by closure of the grid under complex conjugation.
- The reference two-copy entropy decreases as epsilon decreases.
- The basic one-copy entropy deficit grows as
  `r log(1+9/M)+O(1)`; its displayed upper bound is not constant in r.

## Numerical cross-check

Run `python3 lean/scripts/check_prl_parameters.py` from the repository root.
The saved output is in `verification-prl-2026-09-29/parameters.json`.
Both currently specified q values, `4.355e23` and `4.4e23`, satisfy the
trace estimate for `L=2.61e21`. This Decimal computation is explicitly
separate from Lean kernel verification.

See `COVERAGE.md` for the precise representation and capacity scope.

## Current verification result

The fresh 2026-09-29 aggregate run passed with exit code 0: **58 local proof
modules** were rebuilt from source and **2,054 originating declarations**
passed the exhaustive transitive axiom audit. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The successful source manifest
matches the current proof files, including `MainSharperPostprocessing.lean`.

Current record: [`entropy/verification-2026-09-29/verification_status.json`](entropy/verification-2026-09-29/verification_status.json).
