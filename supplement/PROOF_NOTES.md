# Channel construction and formalization

The main theorem is `MainTheorem.main_theorem`. Its only premise is `1 <= N`,
with `N : ℝ`. It proves both strict Holevo inequalities for
`MainTheorem.channelFor N hN`.

The channel is defined in three stages:

1. `MainConcreteBasic.channel` constructs the conjugated-adder tensor family,
   complete Gaussian-integer grid filter, and measurement-and-feedforward map.
2. `MainConcreteSmoothed.channel` applies the finite-field Pauli average after
   identifying the output with `27r` qubits.
3. `MainPauliHolevo.completion` supplies the classical Pauli label and
   conditional output conjugation.

Reality of the filter and measurement is proved. The two-copy argument uses
the actual Bell input, and the one-copy bound covers arbitrary inputs to the
completed channel, including inputs entangled with the label register.

`MainTheorem.main_dimensions` bounds the dimensions of that same channel.
The output dimension is `M^r`; the input dimension is `M^(2r) Q_r^(2r)`.
The extra `M^(2r)` factor is the classical label. The prescribed choice is
`r = 10^11 * Nat.ceil N`.

`MainSharperPostprocessing` proves the sharp slope `d_M(s)-2 log(1+9/M)`
with explicit error `8 log r+4 log 108+2 log beta`, for both the actual
Bell-output entropy and the final channel's two-copy Holevo information.

## Representation conventions

The finite-field construction is instantiated with Mathlib's `GaloisField`.
Character orthogonality, polynomial root bounds, contraction, and seed count
are proved. The specific lexicographic irreducible-polynomial algorithm is
not implemented in this formalization.

Capacity is defined by the regularized Holevo expression. The operational
coding theorem identifying that expression with classical capacity is used
as background rather than reproved.

## Verification

The [verification guide](../lean/README.md) lists every supplemental result,
its Lean declaration, and the commands to build and inspect the proofs.
The [coverage guide](../lean/COVERAGE.md) gives the detailed hypotheses and
scope. The [aggregate record](../lean/entropy/verification/verification_status.json)
contains the successful build and axiom-audit result and exact source hashes.
