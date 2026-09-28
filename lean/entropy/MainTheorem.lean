import MainConcreteSmoothed
import MainPauliHolevo
import MainDimensions

/-!
# A. The main theorem for the explicitly prescribed channels

The only premise of the main result is N ≥ 1. The adder matrices, Gaussian
filter, measurement, finite-field randomizer, and classical Pauli completion
are actual definitions. Their norm, entropy, trace, and twirling properties
are proved in the imported modules, not assumed in this theorem.
-/

set_option maxRecDepth 10000

noncomputable section
open scoped BigOperators
open MainParameters MainFilterParameters MainHolevo

namespace MainTheorem

private lemma M_eq : MainParameters.M = MainFilterParameters.M := by
  norm_num [MainParameters.M]

/-- The quantum input together with the two m-bit classical Pauli labels. -/
abbrev Input (r : ℕ) := Fin (MainConcreteBasic.inputDimension r) ×
  (MainPauli.Bits (27 * r) × MainPauli.Bits (27 * r))

/-- The m output qubits. -/
abbrev Output (r : ℕ) := MainPauli.Bits (27 * r)

/-- The final channel: output randomization followed by the Pauli completion. -/
def channel (r : ℕ) (hr : 1 ≤ r) : CPTPMap (Input r) (Output r) :=
  MainPauliHolevo.completion (MainConcreteSmoothed.channel r hr)

lemma output_card (r : ℕ) : Fintype.card (Output r) = MainFilterParameters.k r := by
  simp only [Output, MainPauli.Bits, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [pow_mul]
  rfl

lemma input_card (r : ℕ) : Fintype.card (Input r) = MainDimensions.inputDimension r := by
  simp only [Input, Fintype.card_prod, Fintype.card_fin,
    show Fintype.card (MainPauli.Bits (27 * r)) = MainFilterParameters.k r from output_card r]
  unfold MainDimensions.inputDimension MainConcreteBasic.inputDimension
  ring

/-- The one-copy Holevo information tends to zero with an explicit bound. -/
theorem one_copy (r : ℕ) (hr : 1 ≤ r) :
    holevo (channel r hr) ≤ Real.log (1 + 1 / (r : ℝ) ^ 2) := by
  have h := MainPauliHolevo.completion_holevo_upper
    (MainConcreteSmoothed.channel r hr) (MainConcreteSmoothed.single_copy r hr)
  rw [show Fintype.card (MainPauli.Bits (27 * r)) = MainFilterParameters.k r
    from output_card r] at h
  change holevo (channel r hr) ≤ _ at h
  simp only [M_eq, MainFilterParameters.k, Nat.cast_pow] at h
  linarith

/-- The actual Bell-and-Pauli ensemble gives a linearly diverging two-copy bound. -/
theorem two_copy (r : ℕ) (hr : 1 ≤ r) :
    (5 : ℝ) / 1000000000 * r - 8 * Real.log r - 4 * Real.log 108 <
      holevo ((channel r hr).prod (channel r hr)) := by
  have he := MainConcreteSmoothed.two_copy r hr
  have hw := MainPauliHolevo.completion_tensor_holevo_lower
    (MainConcreteSmoothed.channel r hr)
    (MState.pure (Ket.MES (Fin (MainConcreteBasic.inputDimension r))))
  rw [show Fintype.card (MainPauli.Bits (27 * r)) = MainFilterParameters.k r
    from output_card r] at hw
  have hn := MainParameters.smoothed_two_copy_gap r hr
  change _ ≤ holevo ((channel r hr).prod (channel r hr)) at hw
  simp only [M_eq, MainFilterParameters.k, Nat.cast_pow] at he hw hn
  calc
    _ < (r : ℝ) * EntropyGapRemainder.entropyDeficit
        (MainFilterParameters.M : ℝ) s0 - 2 * Real.log (randomizerSize r) := hn
    _ = 2 * Real.log ((MainFilterParameters.M : ℝ) ^ r) -
        (2 * Real.log ((MainFilterParameters.M : ℝ) ^ r) -
        (r : ℝ) * EntropyGapRemainder.entropyDeficit (MainFilterParameters.M : ℝ) s0 +
        2 * Real.log (randomizerSize r)) := by ring
    _ ≤ _ := sub_le_sub_left he _
    _ ≤ _ := hw

/-- The explicit channel chosen for a requested real gain N ≥ 1. -/
def channelFor (N : ℝ) (hN : 1 ≤ N) :
    CPTPMap (Input (rFor N)) (Output (rFor N)) :=
  channel (rFor N) (rFor_pos N hN)

/-- The main theorem's two strict Holevo inequalities. -/
theorem main_theorem (N : ℝ) (hN : 1 ≤ N) :
    holevo (channelFor N hN) < 1 / N ∧
      N < holevo ((channelFor N hN).prod (channelFor N hN)) := by
  constructor
  · exact (one_copy (rFor N) (rFor_pos N hN)).trans_lt
      (final_one_copy_threshold N hN)
  · exact (final_two_copy_threshold N hN).trans
      (two_copy (rFor N) (rFor_pos N hN))

/-- Explicit dimension bounds for the very same channels in `main_theorem`. -/
theorem main_dimensions (N : ℝ) (hN : 1 ≤ N) :
    (Real.exp (100000000000 * Real.log (MainParameters.M : ℝ) * N) ≤
        (Fintype.card (Output (rFor N)) : ℝ) ∧
      (Fintype.card (Output (rFor N)) : ℝ) <
        Real.exp (200000000000 * Real.log (MainParameters.M : ℝ) * N)) ∧
    (Real.exp (Real.exp (100000000000 * N)) ≤
        (Fintype.card (Input (rFor N)) : ℝ) ∧
      (Fintype.card (Input (rFor N)) : ℝ) ≤
        Real.exp (Real.exp (40000000000000 * N))) := by
  rw [input_card, output_card]
  constructor
  · simpa only [M_eq, MainFilterParameters.k, Nat.cast_pow] using
      MainParameters.output_dimension_bounds N hN
  · exact MainDimensions.final_input_dimension_bounds N hN

#print axioms main_theorem
#print axioms main_dimensions

end MainTheorem
