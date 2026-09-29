# Mathematical statements and formalization scope

Start with the [verification guide](README.md) for the build command and the
result-to-theorem table. All statements below belong to the unified
[`entropy/`](entropy/) project and are imported by
[`AllProofs.lean`](entropy/AllProofs.lean).

## Entropy and measurement estimates

| Result | Formal statement | Hypotheses and meaning |
| --- | --- | --- |
| Lemma 3 | `SupplementSingle.lemma3` | A channel with the specified matrix-entry formula and the uniform support bound has the stated single-copy entropy lower bound. |
| Hilbert–Schmidt bound | `SupplementSingle.single_copy_hilbertSchmidt_bound` | The bound holds for every input density matrix, giving the pointwise form of the supremum estimate. |
| Lemma 4 | `SupplementEntropy.lemma4` | The measurement relation and mean filter trace bound imply the entropy sandwich for the actual Bell output of the channel and its conjugate. |
| Corollary 1 | `SupplementEntropy.corollary1` | The tensor unitary tuple gives the coordinate-marginal entropy bound; the measurement operator remains global and need not factor. |
| Corollary 2 | `SupplementEntropy.corollary2`, `SupplementEntropy.corollary2_unbounded` | The prescribed support constant and positive entropy-deficit condition imply the gap estimate and unbounded violations. |
| Proposition 2 | `ActualGridSupport.actual_grid_support_bound` | The complete Gaussian-integer grid, finite filter sum, and inverse-square-root measurement operator are defined explicitly. The support bound is proved for arbitrary finite matrix families. |

Channel-entry and conjugate-entry hypotheses specify the channels; they do
not assume the desired entropy conclusions. Coordinate-marginal identities
are derived for arbitrary complex unitary factors. Entropy is the von Neumann
entropy of actual density matrices from Physlib. Logarithms are natural and
Hilbert–Schmidt norms are unnormalized.

## Adder and moment estimates

| Result | Formal statement | Hypotheses and meaning |
| --- | --- | --- |
| Lemma 5 | `SupplementAdder.lemma5_word_trace` | Covers signed words of lengths from 1 to `4*L`, distinguishing whether the actual modular permutation matrix is the identity. |
| Lemma 6 | `SupplementAdder.lemma6_moment_bound` | Gives the matrix-moment estimate with its common Hilbert–Schmidt factor and the stated modulus condition. |
| Proposition 3 | `AdderTrace.technical_trace_bound` | Gives the complete-grid filter trace estimate for the prescribed adder construction, under the parameter assumptions in the statement. |

The computational basis consists of residue-pair tuples and has cardinality
`Q^(2*r)`. `MainAdderTuple` proves the identification of this basis with the
finite input labels used by the channel formalization. Ordered inequalities
use the real part of the complex matrix trace; trace-reality lemmas justify
this convention.

The moment proof uses finitely supported reduced-word convolution. It proves
the stated inequality without reproducing each step of the written
finite-compression argument. The alias
`SupplementAdder.proposition4_trace_bound` refers to the same filter trace
estimate called Proposition 3 in the result table.

## Construction and proof of the main theorem

| Step | Lean declarations |
| --- | --- |
| Adder circuit, unitarity, reality, and tensor enumeration | `MainAdderTuple.generator_circuit`, `MainAdderTuple.generator_unitary`, `MainAdderTuple.generator_real`, `MainAdderTuple.tensorAdderMatrix_eq_tuple`, `MainAdderTuple.enumeratedTuple_eq_finAdderMatrix` |
| Explicit table parameters and filter trace error | `MainFilterParameters.prescribedFilter_small`, `MainFilterParameters.L_pos`, `MainFilterParameters.Q_wordBound`, `MainFilterParameters.a_identity` |
| Equality of the grid/filter representations | `MainGridBridge.fullGridFilter_mat`, `MainGridBridge.enumerated_fullGridFilter_small` |
| Measurement-and-feedforward CPTP map | `MainChannel.fullGridChannel`, `MainChannel.fullGridChannel_entry` |
| Reality and basic-channel entropy bounds | `MainReal.fullGridChannel_real`, `MainConcreteBasic.single_copy`, `MainConcreteBasic.two_copy` |
| Finite-field Pauli contraction and seed count | `MainPauli.fieldSeed_contraction`, `MainConcreteRandomizer.contraction`, `MainConcreteRandomizer.seed_count_bound` |
| Postprocessed entropy bounds | `MainConcreteSmoothed.single_copy`, `MainConcreteSmoothed.two_copy` |
| Positive sharp slope and Bell-output bound | `MainSharperPostprocessing.numerical_margin_sharp`, `MainSharperPostprocessing.two_copy_sharp` |
| Pauli-label extension and Holevo bounds | `MainPauliHolevo.completion_holevo_upper`, `MainPauliHolevo.completion_tensor_holevo_lower`, `MainSharperPostprocessing.holevo_two_copy_sharp` |
| Strict Holevo inequalities for every real `N >= 1` | `MainTheorem.main_theorem` |
| Exact dimensions and growth in `N` | `MainTheorem.input_card`, `MainTheorem.output_card`, `MainTheorem.main_dimensions` |
| All parameter-table growth rates | `MainParameterGrowth.log_P_theta`, `MainParameterGrowth.L_theta`, `MainParameterGrowth.q_theta`, `MainParameterGrowth.log_Q_theta`, `MainParameterGrowth.C₂_theta`, `MainParameterGrowth.log_inputDimension_theta`, `MainParameterGrowth.log_outputDimension_theta` |
| Regularized-capacity gap | `MainCapacityCorollary.main_capacity_gap`, `MainCapacityCorollary.unbounded_capacity_gap` |

`MainTheorem.channelFor` defines the final CPTP map using
`r = 10^11 * Nat.ceil N`. The only premise of `MainTheorem.main_theorem` is
`1 <= N`; the required trace, entropy, randomizer, and Holevo bounds are
proved in its dependencies. `MainTheorem.main_dimensions` concerns the same
channel. The parameter-table growth statements use `Asymptotics.IsTheta`.

The sharp postprocessing endpoints have slope `d_M(s)-2 log(1+9/M)` and
explicit error `8 log r+4 log 108+2 log beta`. The entropy endpoint concerns
the actual Bell output used for the Holevo lower bound.

## Representation and capacity conventions

The randomizer uses Mathlib's `GaloisField 2 t`, its field trace, and explicitly
prescribed Pauli exponents. The contraction and seed-count estimates are
proved. The implementation of the lexicographically first irreducible binary
polynomial and conversion to that specific representation are not formalized.

`MainHolevo.holevo` is a supremum over finite input ensembles.
`MainCapacity.regularizedHolevoCapacity` is the supremum of normalized Holevo
information over actual tensor powers. The capacity-gap theorem uses this
definition. The coding theorem identifying it with operational classical
capacity is background and is not reproved here.

The formalization establishes mathematical statements about the prescribed
channels; it is not an executable, resource-efficient circuit implementation.

## Verification evidence

The [aggregate record](entropy/verification/verification_status.json) covers
58 modules and 2,054 declarations. The verifier rebuilds every local proof
source and follows every declaration's axiom dependencies transitively.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Source hashes
identify the exact versions checked; source scans alone are not treated as
Lean verification.

[Source provenance](source-provenance.json) records source identities and
representation changes. Dependency attribution is in
[`entropy/NOTICE.md`](entropy/NOTICE.md).
