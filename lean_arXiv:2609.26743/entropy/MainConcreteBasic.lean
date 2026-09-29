import MainBasic
import MainAdderTuple
import MainGridBridge
import MainParameters

/-! The fully specified basic adder channel and its two entropy estimates.
All parameters are fixed formulas; the only hypothesis is r ≥ 1. -/

noncomputable section
open scoped BigOperators
open MainFilterParameters ActualTensorBasis MainAdderTuple

namespace MainConcreteBasic

/-- The number of input basis labels in the r-fold register system. -/
def inputDimension (r : ℕ) : ℕ := Q r ^ (2 * r)

instance inputDimension_neZero (r : ℕ) : NeZero (inputDimension r) := by
  constructor
  unfold inputDimension Q
  positivity

/-- The prescribed tensor family in a finite computational basis. -/
def unitaryTuple (r : ℕ) :
    Fin (k r) → Matrix (Fin (inputDimension r)) (Fin (inputDimension r)) ℂ :=
  enumeratedTuple (inputEquiv (2 ^ q r) r) (generator (2 ^ q r) M)

lemma unitaryTuple_unitary (r : ℕ) (i : Fin (k r)) :
    (unitaryTuple r i).conjTranspose * unitaryTuple r i = 1 :=
  enumeratedTuple_unitary _ _ (generator_unitary _ _) i

lemma C₂_pos (r : ℕ) (hr : 1 ≤ r) : 0 < C₂ r := by
  exact lt_of_le_of_lt (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (C₂_large r hr)

/-- The actual measurement-and-feedforward channel with the fixed table parameters. -/
def channel (r : ℕ) (hr : 1 ≤ r) :
    CPTPMap (Fin (inputDimension r)) (Fin (k r)) :=
  MainChannel.fullGridChannel C₁ (by norm_num) (MainGridBridge.k_ge_two r hr)
    (C₂ r) (unitaryTuple r) (unitaryTuple_unitary r) (L r) MainParameters.gamma
    (by norm_num [MainParameters.gamma]) (by norm_num [MainParameters.gamma])

/-- The complete filter meets the fixed trace budget after input reindexing. -/
lemma filter_trace (r : ℕ) (hr : 1 ≤ r) :
    (ActualGridFilterLower.fullGridFilter C₁ (by norm_num) (MainGridBridge.k_ge_two r hr)
      (C₂ r) (unitaryTuple r) (L r)).mat.trace.re ≤
        (inputDimension r : ℝ) * E := by
  have h := MainGridBridge.enumerated_fullGridFilter_small r hr
  have hd : (0 : ℝ) < (Q r : ℝ) ^ (2 * r) := by unfold Q; positivity
  have hb := (div_lt_iff₀ hd).1 h
  have hn : (inputDimension r : ℝ) = (Q r : ℝ) ^ (2 * r) := by
    simp [inputDimension]
  rw [hn]
  change (ActualGridFilterLower.fullGridFilter C₁ (by norm_num)
    (MainGridBridge.k_ge_two r hr) (C₂ r) (unitaryTuple r) (L r)).trace ≤ _
  convert! hb.le using 1 <;> simp only [unitaryTuple, mul_comm]

/-- The exact one-copy Hilbert--Schmidt estimate for every input state. -/
theorem single_copy (r : ℕ) (hr : 1 ≤ r) (ρ : MState (Fin (inputDimension r))) :
    (k r : ℝ) *
      ‖(channel r hr ρ).M - (k r : ℝ)⁻¹ • (1 : HermitianMat (Fin (k r)) ℂ)‖ ^ 2 ≤
        MainParameters.a r - 1 := by
  have h := MainBasic.single_copy C₁ (by norm_num) (MainGridBridge.k_ge_two r hr)
    (C₂ r) (C₂_pos r hr) (unitaryTuple r) (unitaryTuple_unitary r)
    (L r) (L_pos r) MainParameters.gamma
    (by norm_num [MainParameters.gamma]) (by norm_num [MainParameters.gamma]) ρ
  have ha := a_identity r hr MainParameters.gamma
  have ha' : 1 + (C₂ r / (Real.sqrt C₁ - Real.sqrt 2)) ^ 2 *
      MainParameters.gamma ^ 2 / (k r : ℝ) = MainParameters.a r := by
    simpa [MainParameters.a, MainParameters.beta, MainParameters.M] using ha
  change (k r : ℝ) *
      ‖(channel r hr ρ).M - (k r : ℝ)⁻¹ • (1 : HermitianMat (Fin (k r)) ℂ)‖ ^ 2 ≤
        (C₂ r / (Real.sqrt C₁ - Real.sqrt 2)) ^ 2 * MainParameters.gamma ^ 2 / (k r : ℝ) at h
  linarith

lemma reference_entropy :
    SuppressorEntropy.referenceEntropy M MainParameters.gamma E =
      2 * Real.log (M : ℝ) -
        EntropyGapRemainder.entropyDeficit (MainParameters.M : ℝ) MainParameters.s0 := by
  have h := SuppressorEntropy.comparisonEntropy_deficit M (by norm_num) MainParameters.s0
  change 2 * Real.log (M : ℝ) -
      SuppressorEntropy.referenceEntropy M MainParameters.gamma E =
        EntropyGapRemainder.entropyDeficit (MainParameters.M : ℝ) MainParameters.s0 at h
  linarith

/-- The Bell input has a linearly growing entropy deficit for the actual channel. -/
theorem two_copy (r : ℕ) (hr : 1 ≤ r) :
    Sᵥₙ (((channel r hr).prod (channel r hr))
      (MState.pure (Ket.MES (Fin (inputDimension r))))) ≤
      2 * Real.log (k r : ℝ) - (r : ℝ) *
        EntropyGapRemainder.entropyDeficit (MainParameters.M : ℝ) MainParameters.s0 := by
  have hn : 0 < inputDimension r := Nat.pos_of_ne_zero (NeZero.ne _)
  have h := MainBasic.two_copy hn (by norm_num : 2 ≤ M) hr
    (inputEquiv (2 ^ q r) r) (generator (2 ^ q r) M)
    (generator_unitary _ _) (generator_real _ _)
    C₁ (by norm_num) (C₂ r) (L r) MainParameters.gamma E
    (by norm_num [MainParameters.gamma]) (by norm_num [MainParameters.gamma])
    (by norm_num) (filter_trace r hr)
  change Sᵥₙ (((channel r hr).prod (channel r hr))
      (MState.pure (Ket.MES (Fin (inputDimension r))))) ≤
        (r : ℝ) * SuppressorEntropy.referenceEntropy M MainParameters.gamma E at h
  rw [reference_entropy] at h
  have hk : Real.log (k r : ℝ) = (r : ℝ) * Real.log (M : ℝ) := by
    simp [k, Real.log_pow]
  rw [hk]
  nlinarith

#print axioms single_copy
#print axioms two_copy

end MainConcreteBasic
