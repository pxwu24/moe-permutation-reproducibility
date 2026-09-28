import MainHolevoTensor
import MainFlaggedEntropy
import MainPauli
import MainPauliTensor

/-! The concrete Pauli completion and its Holevo information. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open scoped BigOperators Matrix

namespace MainHolevo
variable {d ι : Type} [Fintype d] [Fintype ι] [DecidableEq d]

/-- Matrix formula for a uniform ensemble average. -/
theorem average_uniform_m [Nonempty ι] (ρ : ι → MState d) :
    (average ProbDistribution.uniform ρ).m =
      (Fintype.card ι : ℂ)⁻¹ • ∑ i, (ρ i).m := by
  change (average ProbDistribution.uniform ρ).M.mat = _
  rw [average_M]
  simp only [HermitianMat.mat_finset_sum, HermitianMat.mat_smul,
    ProbDistribution.uniform_def, Finset.card_univ, one_div]
  ext a b
  simp [Matrix.sum_apply, Complex.real_smul, Finset.mul_sum, MState.m, -MState.mat_M]

/-- A matrix twirling identity gives the corresponding identity of states. -/
theorem average_twirl_state [Nonempty ι] [Nonempty d]
    (U : ι → Matrix.unitaryGroup d ℂ)
    (hU : ∀ A : Matrix d d ℂ,
      (Fintype.card ι : ℂ)⁻¹ • ∑ i, (U i).val * A * ((U i).val).conjTranspose =
        ((Fintype.card d : ℂ)⁻¹ * Matrix.trace A) • 1)
    (ρ : MState d) :
    average ProbDistribution.uniform (fun i ↦ ρ.uConj (U i)) = MState.uniform := by
  apply MState.ext_m
  rw [average_uniform_m]
  change (Fintype.card ι : ℂ)⁻¹ •
    ∑ i, (U i).val * ρ.m * ((U i).val).conjTranspose = _
  rw [hU, ρ.tr', mul_one]
  ext a b
  change (Fintype.card d : ℂ)⁻¹ * (if a = b then 1 else 0) =
    if a = b then ((ProbDistribution.uniform a : ℝ) : ℂ) else 0
  simp [ProbDistribution.uniform_def]

end MainHolevo

namespace MainPauliHolevo
open MainHolevo MainPauli

/-- The explicit Pauli matrices, bundled with their proved unitarity. -/
def pauliUnitary {m : ℕ} (v : Bits m × Bits m) :
    Matrix.unitaryGroup (Bits m) ℂ :=
  ⟨pauli v.1 v.2, Matrix.mem_unitaryGroup_iff.mpr (pauli_unitary_right _ _)⟩

theorem pauli_twirl_state {m : ℕ} (ρ : MState (Bits m)) :
    MainHolevo.average ProbDistribution.uniform
      (fun v : Bits m × Bits m ↦ ρ.uConj (pauliUnitary v)) = MState.uniform := by
  apply MState.ext_m
  rw [average_uniform_m]
  have h := pauli_twirl ρ.m
  have heq : (Fintype.card (Bits m × Bits m) : ℂ)⁻¹ •
      ∑ v : Bits m × Bits m, (ρ.uConj (pauliUnitary v)).m =
        MainPauli.average (fun v : Bits m × Bits m ↦ v) ρ.m := by
    simp only [MainPauli.average, LinearMap.smul_apply, LinearMap.sum_apply,
      MainPauli.conjugate, pauliUnitary, MState.uConj, MState.m]
    rfl
  rw [heq, h, ρ.tr', mul_one]
  ext a b
  change (Fintype.card (Bits m) : ℂ)⁻¹ * (if a = b then 1 else 0) =
    if a = b then ((ProbDistribution.uniform a : ℝ) : ℂ) else 0
  simp [ProbDistribution.uniform_def]

/-- The completion uses exactly k² flags when the output dimension is k. -/
def completion {n : Type} [Fintype n] [DecidableEq n] {m : ℕ}
    (Φ : CPTPMap n (Bits m)) : CPTPMap (n × (Bits m × Bits m)) (Bits m) :=
  flaggedExtension Φ pauliUnitary

/-- An arbitrary output yields a concrete one-copy Holevo lower bound. -/
theorem completion_holevo_lower {n : Type} [Fintype n] [DecidableEq n] {m : ℕ}
    (Φ : CPTPMap n (Bits m)) (ρ : MState n) :
    Real.log (Fintype.card (Bits m)) - Sᵥₙ (Φ ρ) ≤ holevo (completion Φ) := by
  exact orbit_ensembleHolevo (completion Φ)
    (fun v ↦ ρ ⊗ᴹ MState.pure (Ket.basis v)) (Φ ρ) pauliUnitary
    (fun v ↦ flaggedExtension_basis Φ pauliUnitary ρ v) (pauli_twirl_state (Φ ρ))

/-- The completed channel obeys the same single-copy entropy lower bound. -/
theorem completion_holevo_upper {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {m : ℕ} (Φ : CPTPMap n (Bits m)) {h : ℝ}
    (hS : ∀ ρ, h ≤ Sᵥₙ (Φ ρ)) :
    holevo (completion Φ) ≤ Real.log (Fintype.card (Bits m)) - h := by
  apply holevo_le_of_entropy_lower
  exact MainFlaggedEntropy.flaggedExtension_entropy_lower Φ pauliUnitary hS

/-- The familiar Weyl-completion identity, obtained from the actual orbit
ensemble and the entropy lower bound for arbitrary flagged inputs. -/
theorem completion_holevo_eq {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {m : ℕ} (Φ : CPTPMap n (Bits m)) :
    holevo (completion Φ) = Real.log (Fintype.card (Bits m)) -
      SuppressorEntropy.minimumOutputEntropy Φ := by
  apply le_antisymm
  · exact completion_holevo_upper Φ (SuppressorEntropy.minimumOutputEntropy_le Φ)
  · have h : Real.log (Fintype.card (Bits m)) - holevo (completion Φ) ≤
        SuppressorEntropy.minimumOutputEntropy Φ := by
      apply le_csInf (Set.range_nonempty _)
      rintro x ⟨ρ, rfl⟩
      have hρ := completion_holevo_lower Φ ρ
      linarith
    linarith

/-- The full independent Pauli orbit also twirls every bipartite state,
including entangled states, to the maximally mixed state. -/
theorem tensor_pauli_twirl_state {m : ℕ} (ρ : MState (Bits m × Bits m)) :
    MainHolevo.average ProbDistribution.uniform
      (fun v : (Bits m × Bits m) × (Bits m × Bits m) ↦
        ρ.uConj ((pauliUnitary v.1) ⊗ᵤ (pauliUnitary v.2))) = MState.uniform := by
  apply average_twirl_state
  intro A
  convert MainPauliTensor.tensor_pauli_twirl m A using 1
  simp only [MainPauliTensor.tensorAverage, LinearMap.smul_apply,
    LinearMap.sum_apply, MainPauliTensor.tensorConjugate,
    LinearMap.coe_mk, AddHom.coe_mk, MainPauliTensor.tensorPauli, pauliUnitary]
  rfl

/-- A specified entangled input gives the two-copy Holevo lower bound for the
actual tensor square of the completed channel. -/
theorem completion_tensor_holevo_lower {n : Type} [Fintype n] [DecidableEq n]
    {m : ℕ} (Φ : CPTPMap n (Bits m)) (ρ : MState (n × n)) :
    2 * Real.log (Fintype.card (Bits m)) - Sᵥₙ ((Φ ⊗ᶜᵖ Φ) ρ) ≤
      holevo ((completion Φ) ⊗ᶜᵖ (completion Φ)) := by
  exact flaggedExtension_tensor_holevo_lower Φ pauliUnitary ρ
    (tensor_pauli_twirl_state ((Φ ⊗ᶜᵖ Φ) ρ))

end MainPauliHolevo
