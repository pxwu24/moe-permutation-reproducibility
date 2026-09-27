# Supplement-to-Lean coverage

Result numbers and page numbers refer to the supplied 18-page version of
*Explicit channels with unbounded gains in classical communication using
entangled inputs*. Its SHA-256 is recorded in `source-provenance.json`.

| Result | Paper | Project and proof source | Principal declarations |
| --- | --- | --- | --- |
| Lemma 3: single-copy estimate | pp. 7–8; S4–S5 | `entropy/SingleChannel.lean`, `entropy/SupplementSingle.lean` | `SupplementSingle.lemma3`; `SupplementSingle.single_copy_hilbertSchmidt_bound` and `SuppressorEntropy.single_copy_lemma` |
| Lemma 4: two-copy estimate | pp. 8–10; S9 | `entropy/JointChannel.lean`, `entropy/SupplementEntropy.lean` | `SupplementEntropy.lemma4` (including the Bell-input bound) |
| Corollary 1: tensor-coordinate estimate | p. 10; S22 | `entropy/SupplementEntropy.lean` and the marginal modules | `SupplementEntropy.corollary1` |
| Corollary 2: linear and unbounded entropy gap | p. 10; S24 | `entropy/SupplementEntropy.lean`, `entropy/SymbolicAmplification.lean` | `SupplementEntropy.corollary2` and `SupplementEntropy.corollary2_unbounded` |
| Proposition 3: uniform measurement estimate | pp. 11–12; S25 | `entropy/ActualGridSupport.lean` | `ActualGridSupport.actual_grid_support_bound` |
| Proposition 4: filter trace estimate | pp. 13, 17; S31 | `adder-trace/AdderTrace.lean` | `AdderTrace.technical_trace_bound` |
| Lemma 5: word trace estimate | pp. 13–14; S33 | `adder-trace/SupplementAdder.lean` | `SupplementAdder.lemma5_word_trace` |
| Lemma 6: matrix moment estimate | pp. 14–17; S35 | `adder-trace/SupplementAdder.lean` | `SupplementAdder.lemma6_moment_bound` |

## Interpreting the statements

- The entropy project uses actual density matrices, channels, and von Neumann
  entropy from Physlib. Conditions specifying matrix entries or the conjugate
  channel express the definitions in the paper; they do not assume the desired
  entropy or marginal bound.
- The single-copy Hilbert–Schmidt inequality is stated for every input density
  matrix. This is the pointwise form of the supremum bound in S4.
- The general tensor estimate concerns the channel and its entrywise conjugate.
  A theorem restricted to real unitaries would not, by itself, cover the full
  statement of Corollary 1.
- Proposition 3 is proved for arbitrary finite matrix families, which is
  stronger than the unitary case in the paper. The actual grid, filter, and
  inverse-square-root measurement operator are defined in the proof.
- The adder project uses the computational basis of residue-pair tuples,
  whose cardinality is exactly `Q^(2*r)`, and a finite relabeling of the unitary
  index set by `Fin (M^r)`.
- Lemma 5 branches on the actual modular permutation matrix being the
  identity and covers every length from 1 through `4*L`.
- Lemma 6 has the exact common Hilbert–Schmidt factor and exponent `L` on
  `k*(k-1)`. Its formal proof uses finitely supported reduced-word convolution;
  this verifies the stated inequality without formalizing the paper's
  particular finite-compression presentation.
- Ordered matrix-trace inequalities use the real part of the complex trace.
  Hermitian trace-reality results supply the identification with the paper's
  real trace. All logarithms are natural.

## Exclusion

The section **Details in the proof of the main theorem** beginning on page 17,
including the channel `R_r`, the final Holevo-information theorem, and the
parameter/dimension analysis in Table II, is not part of this collection.
Earlier formalizations for a different finite-group construction are also
not presented as proofs of that missing section.

## Note on the written proof of Lemma 5

Cancelling adjacent inverse letters alone does not make every interior power
of `P` nonzero: adjacent equal indices with the same sign can remain, as in
`T_i T_i`. Before the cone argument, group each maximal run of equal indices
into one nonzero power of `T_i`. Consecutive grouped indices are then distinct.
Keep the original signed-letter list for the quantitative length bound.
The formal proof does not assume the problematic intermediate claim and
proves the stated bound without changing its constants.

## Verification records

Both clean verification runs finished with exit code 0. The entropy project
recompiled all 30 local proof modules and audited 584 declarations. The adder
project rebuilt both proof modules and audited 615 theorems. Only `propext`,
`Classical.choice`, and `Quot.sound` occurred in the transitive axiom
dependencies. There are no proof placeholders or added mathematical axioms.

`source-provenance.json` records the hashes of the recovered original sources.
Each project keeps its compiler and axiom-audit records in its `verification/`
directory. Historical records are labeled separately from fresh checks of
this collection. A successful source scan alone is not counted as a Lean
verification; the verification scripts compile the proofs and audit their
transitive axiom dependencies.
