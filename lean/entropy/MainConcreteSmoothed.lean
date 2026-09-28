import MainSmoothedChannel
import MainConcreteBasic
import MainHolevoTensor

/-! The fully specified randomized adder channel and both entropy bounds. -/
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators RealInnerProductSpace
open MainPauli MainSmoothedChannel

namespace MainConcreteSmoothed

private theorem M_eq : MainParameters.M = MainFilterParameters.M := by
  norm_num [MainParameters.M]

def outputEquiv (r : ℕ) : Fin (MainFilterParameters.k r) ≃ Bits (27 * r) :=
  (Fintype.equivFinOfCardEq (by
    simpa [MainFilterParameters.k, MainParameters.M] using
      MainConcreteRandomizer.card_output r)).symm

theorem norm_reindex_sq {d e : Type} [Fintype d] [Fintype e]
    [DecidableEq d] [DecidableEq e] (A : HermitianMat d ℂ) (eqv : d ≃ e) :
    ‖A.reindex eqv‖ ^ 2 = ‖A‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, HermitianMat.reindex_inner,
    HermitianMat.reindex_reindex, Equiv.self_trans_symm, HermitianMat.reindex_refl]

theorem centered_relabel_norm_sq {d e : Type} [Fintype d] [Fintype e]
    [DecidableEq d] [DecidableEq e] (ρ : MState d) (eqv : e ≃ d) (c : ℝ) :
    ‖(ρ.relabel eqv).M - c • (1 : HermitianMat e ℂ)‖ ^ 2 =
      ‖ρ.M - c • (1 : HermitianMat d ℂ)‖ ^ 2 := by
  change ‖ρ.M.reindex eqv.symm - c • (1 : HermitianMat e ℂ)‖ ^ 2 = _
  rw [← HermitianMat.reindex_one (e := eqv.symm), ← HermitianMat.reindex_smul,
    HermitianMat.reindex_sub, norm_reindex_sq]

/-- Relabel the basic output as its 27r qubits. -/
def basicBits (r : ℕ) (hr : 1 ≤ r) :
    CPTPMap (Fin (MainConcreteBasic.inputDimension r)) (Bits (27 * r)) :=
  CPTPMap.ofEquiv (outputEquiv r) ∘ₘ MainConcreteBasic.channel r hr

/-- The actual channel before the final Weyl completion. -/
def channel (r : ℕ) (hr : 1 ≤ r) :
    CPTPMap (Fin (MainConcreteBasic.inputDimension r)) (Bits (27 * r)) :=
  randomizer r ∘ₘ basicBits r hr

theorem basicBits_hilbertSchmidt (r : ℕ) (hr : 1 ≤ r)
    (ρ : MState (Fin (MainConcreteBasic.inputDimension r))) :
    (MainParameters.M ^ r : ℝ) *
      ‖(basicBits r hr ρ).M - (MainParameters.M ^ r : ℝ)⁻¹ •
        (1 : HermitianMat (Bits (27 * r)) ℂ)‖ ^ 2 ≤ MainParameters.a r - 1 := by
  simp only [basicBits, CPTPMap.compose_eq, CPTPMap.ofEquiv_apply,
    centered_relabel_norm_sq]
  simpa only [M_eq, MainFilterParameters.k, Nat.cast_pow] using
    MainConcreteBasic.single_copy r hr ρ

/-- Unconditional one-copy entropy bound for the fully specified channel. -/
theorem single_copy (r : ℕ) (hr : 1 ≤ r)
    (ρ : MState (Fin (MainConcreteBasic.inputDimension r))) :
    Real.log (MainParameters.M ^ r) - Real.log (1 + 1 / (r : ℝ) ^ 2) ≤
      Sᵥₙ (channel r hr ρ) :=
  smoothed_entropy r hr (basicBits r hr) (basicBits_hilbertSchmidt r hr) ρ

theorem ofEquiv_prod_state {d e : Type} [Fintype d] [Fintype e]
    [DecidableEq d] [DecidableEq e] (eqv : d ≃ e) (ρ : MState (d × d)) :
    ((CPTPMap.ofEquiv eqv ⊗ᶜᵖ CPTPMap.ofEquiv eqv) ρ) =
      ρ.relabel (Equiv.prodCongr eqv.symm eqv.symm) := by
  apply MState.ext_m
  change ((MatrixMap.submatrix ℂ eqv.symm).kron
    (MatrixMap.submatrix ℂ eqv.symm)) ρ.m = _
  rw [MatrixMap.submatrix_kron_submatrix]
  rfl

theorem basicBits_two_copy (r : ℕ) (hr : 1 ≤ r) :
    Sᵥₙ ((basicBits r hr ⊗ᶜᵖ basicBits r hr)
      (MState.pure (Ket.MES (Fin (MainConcreteBasic.inputDimension r))))) ≤
      2 * Real.log (MainParameters.M ^ r) - (r : ℝ) *
        EntropyGapRemainder.entropyDeficit (MainParameters.M : ℝ) MainParameters.s0 := by
  rw [basicBits, MainHolevo.channel_prod_comp, CPTPMap.compose_eq,
    ofEquiv_prod_state, Sᵥₙ_relabel]
  simpa only [M_eq, MainFilterParameters.k, Nat.cast_pow] using
    MainConcreteBasic.two_copy r hr

/-- Unconditional two-copy Bell entropy bound after the actual randomization. -/
theorem two_copy (r : ℕ) (hr : 1 ≤ r) :
    Sᵥₙ ((channel r hr ⊗ᶜᵖ channel r hr)
      (MState.pure (Ket.MES (Fin (MainConcreteBasic.inputDimension r))))) ≤
      2 * Real.log (MainParameters.M ^ r) - (r : ℝ) *
        EntropyGapRemainder.entropyDeficit (MainParameters.M : ℝ) MainParameters.s0 +
        2 * Real.log (MainParameters.randomizerSize r) := by
  rw [channel, MainHolevo.channel_prod_comp, CPTPMap.compose_eq]
  have h := uniformChannel_tensor_entropy
    (fun i ↦ pauliUnitary (MainConcreteRandomizer.seeds r i))
    ((basicBits r hr ⊗ᶜᵖ basicBits r hr)
      (MState.pure (Ket.MES (Fin (MainConcreteBasic.inputDimension r)))))
  rw [MainConcreteRandomizer.card_seeds r hr] at h
  have hb := basicBits_two_copy r hr
  change Sᵥₙ ((uniformChannel (fun i ↦ pauliUnitary (MainConcreteRandomizer.seeds r i)) ⊗ᶜᵖ
    uniformChannel (fun i ↦ pauliUnitary (MainConcreteRandomizer.seeds r i)))
    ((basicBits r hr ⊗ᶜᵖ basicBits r hr)
      (MState.pure (Ket.MES (Fin (MainConcreteBasic.inputDimension r)))))) ≤ _
  linarith

end MainConcreteSmoothed

#print axioms MainConcreteSmoothed.single_copy
#print axioms MainConcreteSmoothed.two_copy
