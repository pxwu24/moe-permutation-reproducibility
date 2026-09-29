# Proof and formalization notes

The main theorem is represented by `MainTheorem.main_theorem`. Its only premise is `1 ≤ N`, with `N : ℝ`. It proves the two strict Holevo inequalities for the channel `MainTheorem.channelFor N hN`. In particular, the theorem does not assume a trace estimate, a randomizer, an entropy bound, or a successful parameter choice.

The channel is constructed through the following stages:

1. `MainConcreteBasic.channel`: the actual conjugated-adder tensor family, the complete Gaussian-integer grid filter, and the measurement-and-feedforward CPTP map.
2. `MainConcreteSmoothed.channel`: the finite-field Pauli average applied to that channel, after identifying its output basis with `27r` qubits.
3. `MainPauliHolevo.completion`: the specified classical Pauli label and controlled output conjugation.

The reality of the filter and measurement operator is proved, so the conjugate-channel estimate applies to the actual tensor square. The two-copy proof uses the actual Bell input. The one-copy bound for the completed channel covers arbitrary flagged inputs, including inputs entangled with the flag; its proof constructs the normalized positive diagonal blocks explicitly.

`MainTheorem.output_card`, `input_card`, and `main_dimensions` concern these same channels. They give output dimension `M^r` and input dimension `M^(2r) Q_r^(2r)`, together with explicit exponential and double-exponential bounds in `N`. The randomizer itself does not enlarge the input: the extra `M^(2r)` factor comes from the final classical label.

## Finite-field presentation and basis labels

The manuscript specifies a polynomial presentation of the field by choosing the first irreducible polynomial in a fixed ordering. Lean proves the character and polynomial-root estimates for an arbitrary finite field over `F₂`, then instantiates Mathlib's `GaloisField 2 t`. It does not implement or verify the lexicographic polynomial-search algorithm.

This presentation choice does not affect the averaged Pauli channel: a field isomorphism preserves powers and the field trace and bijectively relabels the pairs `(x,y)`. Thus it preserves the complete multiset of Pauli conjugations. This explanation of presentation independence is mathematical; the project does not include a separate theorem identifying the lexicographic implementation with Mathlib's presentation. Likewise, computational-basis enumerations are represented by finite equivalences, with the required norm, trace, and entropy invariance proved. The code is a mathematical formalization, not an executable resource-efficient channel implementation.

## Capacity interpretation

`MainCapacity` defines capacity by the regularized Holevo formula and proves the two-copy lower bound and the ensuing gap. `MainCapacityCorollary` applies this to the constructed family. The standard coding characterization that identifies this regularized expression with operational classical capacity is background used by the paper; the project does not reprove that coding theorem.

## Inserting the LaTeX

Replace the old main-proof subsection **and its parameter table** with `main_theorem.tex`. The replacement intentionally reuses `subsec:technical-main-proof`, `tab:all-r`, and `eq:q-choice`. There are no duplicate labels or unresolved internal references inside the replacement.

In the earlier manuscript, the uniform measurement estimate is **Proposition 2** and the adder trace estimate is **Proposition 3**. Lemmas 3–4 and Corollary 1 retain those numbers. Some Lean declarations retain the earlier manuscript's proposition numbering; their mathematical statements are unchanged. The 2026-09-29 revision restores the supplied source label names for cross-references, avoiding hard-coded proposition and lemma numbers.

Compilation and axiom-audit results are recorded in the project's verification logs. The final main-result endpoints are checked against the same standard-axiom policy as the earlier supplement results; no additional mathematical hypothesis is hidden in an unchecked certificate.

## Revised asymptotic statement (2026-09-29)

The new `MainSharperPostprocessing` module proves the sharper coefficient
`d_M(s)-2 log(1+9/M)`, with error
`8 log r+4 log 108+2 log beta`. Both the actual Bell-output entropy statement
and its final-channel Holevo consequence are formalized. The previously
proved conservative numerical estimate and `r_N=10^11 ceil(N)` are retained.

The final uploaded supplement omitted the randomizer definition and proof.
This repository's complete `main_theorem.tex` supplies that essential step.
A bound on minimum output entropy alone cannot justify an entropy bound
for the particular Bell input; the proof and new endpoint give the latter.
