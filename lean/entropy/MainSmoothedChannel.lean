import MainSmoothing
import MainHolevo
import MainConcreteRandomizer

/-! Actual uniformly mixed-unitary channels and the explicit smoothing step. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder Kronecker
open MainPauli MainHolevo MainSmoothing

namespace MainSmoothedChannel

variable {n d e ι κ : Type} [Fintype n] [Fintype d] [Fintype e]
variable [Fintype ι] [Fintype κ] [DecidableEq n] [DecidableEq d] [DecidableEq e]

def uniformChannel [Nonempty ι] (U : ι → Matrix.unitaryGroup d ℂ) : CPTPMap d d where
  toLinearMap := (Fintype.card ι : ℂ)⁻¹ • ∑ i, (CPTPMap.ofUnitary (U i)).map
  cp := (MatrixMap.IsCompletelyPositive.finset_sum
    (fun i ↦ (CPTPMap.ofUnitary (U i)).cp)).smul (by positivity)
  TP X := by
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    change ((Fintype.card ι : ℂ)⁻¹ •
      ∑ i, (CPTPMap.ofUnitary (U i)).map X).trace = X.trace
    rw [Matrix.trace_smul, Matrix.trace_sum]
    simp_rw [(CPTPMap.ofUnitary (U _)).TP X]
    simp [nsmul_eq_mul, Fintype.card_ne_zero]

theorem uniformChannel_map [Nonempty ι] (U : ι → Matrix.unitaryGroup d ℂ)
    (X : Matrix d d ℂ) :
    (uniformChannel U).map X = (Fintype.card ι : ℂ)⁻¹ •
      ∑ i, (U i).val * X * (U i).val.conjTranspose := by
  change (((Fintype.card ι : ℂ)⁻¹ • ∑ i, MatrixMap.conj (U i).val) X) = _
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

theorem uniformChannel_state [Nonempty ι] (U : ι → Matrix.unitaryGroup d ℂ)
    (ρ : MState d) :
    uniformChannel U ρ = average ProbDistribution.uniform (fun i ↦ ρ.uConj (U i)) := by
  apply MState.ext_m
  rw [CPTPMap.mat_coe_eq_apply_mat, uniformChannel_map]
  change _ = (average ProbDistribution.uniform (fun i ↦ ρ.uConj (U i))).M.mat
  rw [average_M, HermitianMat.mat_finset_sum]
  simp only [HermitianMat.mat_smul, ProbDistribution.uniform_def,
    Finset.card_univ, one_div, MState.uConj, HermitianMat.conj_apply_mat]
  ext a b
  simp [Matrix.smul_apply, Matrix.sum_apply, Complex.real_smul, Finset.mul_sum]

theorem uniformChannel_entropy [Nonempty ι] (U : ι → Matrix.unitaryGroup d ℂ)
    (ρ : MState d) :
    Sᵥₙ (uniformChannel U ρ) ≤ Sᵥₙ ρ + Real.log (Fintype.card ι) := by
  classical
  rw [uniformChannel_state]
  exact entropy_uniform_mixture U ρ

private theorem sum_kron_left (f : ι → MatrixMap d d ℂ)
    (T : MatrixMap e e ℂ) :
    (∑ i, f i).kron T = ∑ i, (f i).kron T := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [MatrixMap.zero_kron]
  | @insert a s ha ih => simp [ha, ih, MatrixMap.add_kron]

private theorem sum_kron_right (T : MatrixMap d d ℂ)
    (f : κ → MatrixMap e e ℂ) :
    T.kron (∑ i, f i) = ∑ i, T.kron (f i) := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp [MatrixMap.kron_zero]
  | @insert a s ha ih => simp [ha, ih, MatrixMap.kron_add]

/-- Independent uniform conjugations are the uniform tensor-product family. -/
theorem uniformChannel_prod [Nonempty ι] [Nonempty κ]
    (U : ι → Matrix.unitaryGroup d ℂ) (V : κ → Matrix.unitaryGroup e ℂ) :
    uniformChannel U ⊗ᶜᵖ uniformChannel V =
      uniformChannel (fun ij : ι × κ ↦ Matrix.unitary_kron (U ij.1) (V ij.2)) := by
  apply CPTPMap.funext
  intro ρ
  apply MState.ext_m
  change ((uniformChannel U).map.kron (uniformChannel V).map) ρ.m =
    (uniformChannel (fun ij : ι × κ ↦ Matrix.unitary_kron (U ij.1) (V ij.2))).map ρ.m
  congr 1
  change ((Fintype.card ι : ℂ)⁻¹ • ∑ i, MatrixMap.conj (U i).val).kron
      ((Fintype.card κ : ℂ)⁻¹ • ∑ i, MatrixMap.conj (V i).val) =
    (Fintype.card (ι × κ) : ℂ)⁻¹ •
      ∑ ij : ι × κ, MatrixMap.conj (Matrix.unitary_kron (U ij.1) (V ij.2)).val
  rw [MatrixMap.smul_kron, MatrixMap.kron_smul, sum_kron_left]
  simp_rw [sum_kron_right, MatrixMap.conj_kron]
  simp [Fintype.card_prod, Nat.cast_mul, mul_inv_rev, smul_smul,
    Fintype.sum_prod_type, Matrix.unitary_kron, mul_comm]

theorem uniformChannel_tensor_entropy [Nonempty ι]
    (U : ι → Matrix.unitaryGroup d ℂ) (ρ : MState (d × d)) :
    Sᵥₙ ((uniformChannel U ⊗ᶜᵖ uniformChannel U) ρ) ≤
      Sᵥₙ ρ + 2 * Real.log (Fintype.card ι) := by
  rw [uniformChannel_prod]
  have h := uniformChannel_entropy
    (fun ij : ι × ι ↦ Matrix.unitary_kron (U ij.1) (U ij.2)) ρ
  simpa only [Fintype.card_prod, Nat.cast_mul,
    Real.log_mul (by positivity : (Fintype.card ι : ℝ) ≠ 0)
      (by positivity : (Fintype.card ι : ℝ) ≠ 0), two_mul] using h

def pauliUnitary {m : ℕ} (v : Bits m × Bits m) : Matrix.unitaryGroup (Bits m) ℂ :=
  ⟨pauli v.1 v.2, Matrix.mem_unitaryGroup_iff.mpr (pauli_unitary_right v.1 v.2)⟩

theorem pauli_uniformChannel_map {m : ℕ} [Nonempty ι]
    (seed : ι → Bits m × Bits m) :
    (uniformChannel (fun i ↦ pauliUnitary (seed i))).map = MainPauli.average seed := by
  rfl

theorem vectorize_norm_sq_eq {m : ℕ} (X : Matrix (Bits m) (Bits m) ℂ) :
    ‖vectorize X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [vectorize, Fintype.sum_prod_type]

def randomizer (r : ℕ) : CPTPMap (Bits (27 * r)) (Bits (27 * r)) :=
  uniformChannel (fun i ↦ pauliUnitary (MainConcreteRandomizer.seeds r i))

theorem randomizer_map (r : ℕ) :
    (randomizer r).map = MainPauli.average (MainConcreteRandomizer.seeds r) := rfl

theorem randomizer_one (r : ℕ) : (randomizer r).map 1 = 1 := by
  rw [randomizer_map]
  exact average_one _

theorem randomizer_contraction (r : ℕ) (hr : 0 < r)
    (Y : Matrix (Bits (27 * r)) (Bits (27 * r)) ℂ) (hY : Y.trace = 0) :
    (∑ i, ∑ j, ‖(randomizer r).map Y i j‖ ^ 2) ≤
      (∑ i, ∑ j, ‖Y i j‖ ^ 2) / ((r : ℝ) ^ 2 * MainParameters.a r) := by
  rw [randomizer_map, ← vectorize_norm_sq_eq, ← vectorize_norm_sq_eq]
  exact MainConcreteRandomizer.contraction r hr Y hY

/-- The actual finite-field randomizer produces the claimed one-copy entropy. -/
theorem smoothed_entropy (r : ℕ) (hr : 0 < r)
    (Φ : CPTPMap n (Bits (27 * r)))
    (hbasic : ∀ ρ, (MainParameters.M ^ r : ℝ) *
      ‖(Φ ρ).M - (MainParameters.M ^ r : ℝ)⁻¹ •
        (1 : HermitianMat (Bits (27 * r)) ℂ)‖ ^ 2 ≤ MainParameters.a r - 1)
    (ρ : MState n) :
    Real.log (MainParameters.M ^ r) - Real.log (1 + 1 / (r : ℝ) ^ 2) ≤
      Sᵥₙ ((randomizer r ∘ₘ Φ) ρ) := by
  have hc := MainConcreteRandomizer.card_output r
  have hb : ∀ ρ, (Fintype.card (Bits (27 * r)) : ℝ) *
      ‖(Φ ρ).M - (Fintype.card (Bits (27 * r)) : ℝ)⁻¹ •
        (1 : HermitianMat (Bits (27 * r)) ℂ)‖ ^ 2 ≤ MainParameters.a r - 1 := by
    simpa only [hc, Nat.cast_pow] using hbasic
  simpa only [hc, Nat.cast_pow] using
    cptp_smoothed_entropy (randomizer r) Φ (randomizer_one r)
      (r : ℝ) (MainParameters.a r) (by exact_mod_cast hr) (MainParameters.a_pos r)
      (by positivity) (randomizer_contraction r hr) hb ρ

end MainSmoothedChannel

#print axioms MainSmoothedChannel.smoothed_entropy
