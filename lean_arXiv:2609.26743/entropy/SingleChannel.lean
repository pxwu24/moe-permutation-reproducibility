import SingleEntropy
import BellAlgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order

/-! The single-copy lemma for a state-valued map with exactly the prescribed
matrix entries. The matrix norm is the Euclidean operator norm; the norm on
HermitianMat is the unnormalized Hilbert--Schmidt norm. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
open EntropyLemmas.BellAlgebra

namespace SuppressorEntropy

variable {n k : ℕ}

def testObservable (H : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (W : HermitianMat (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  H * (∑ i, ∑ j, W i j • ((U i).conjTranspose * U j)) * H

lemma testObservable_isHermitian (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (W : HermitianMat (Fin k) ℂ) : (testObservable H U W).IsHermitian := by
  have hW (i j : Fin k) : star (W i j) = W j i := by
    change star (W.mat i j) = W.mat j i
    exact congrFun (congrFun W.H j) i
  change (testObservable H U W).conjTranspose = testObservable H U W
  unfold testObservable
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, hH.eq, hW]
  rw [Finset.sum_comm]
  simp only [Matrix.mul_assoc]

lemma state_inner_le_operatorNorm (ρ : MState (Fin n))
    (B : HermitianMat (Fin n) ℂ) :
    inner ℝ ρ.M B ≤ ‖B.mat‖ := by
  have hB : B ≤ ‖B.mat‖ • (1 : HermitianMat (Fin n) ℂ) := by
    open MatrixOrder in
    have h := IsSelfAdjoint.le_algebraMap_norm_self
      (Matrix.isHermitian_iff_isSelfAdjoint.mp B.H)
    change B.mat ≤ (‖B.mat‖ • (1 : HermitianMat (Fin n) ℂ)).mat
    simpa [Algebra.algebraMap_eq_smul_one] using h
  have h := HermitianMat.inner_mono ρ.nonneg hB
  simpa using h

lemma suppressor_output_diagonal (H : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (Φ : MState (Fin n) → MState (Fin k))
    (hΦ : ∀ ρ i j, (Φ ρ).m i j = channelEntry (suppressorK H U) ρ.m i j)
    (ρ : MState (Fin n)) (i : Fin k) :
    (Φ ρ).m i i = (k : ℂ)⁻¹ := by
  rw [hΦ]
  unfold channelEntry
  rw [suppressorK_diagonal H U hU]
  simp [ρ.tr']

/-- The full single-copy lemma. The defining-entry premise specifies precisely
the user's channel, without postulating any entropy or norm consequence. -/
theorem single_copy_lemma [Nonempty (Fin n)]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (Φ : MState (Fin n) → MState (Fin k))
    (hΦ : ∀ ρ i j, (Φ ρ).m i j = channelEntry (suppressorK H U) ρ.m i j)
    (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hk : 0 < k)
    (hbound : ∀ W : HermitianMat (Fin k) ℂ, (∀ i, W i i = 0) →
      ‖testObservable H U W‖ ≤ C * γ * ‖W‖) :
    Real.log k - Real.log (1 + C^2 * γ^2 / k) ≤ minimumOutputEntropy Φ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  suffices hresult : Real.log (Fintype.card (Fin k)) -
      Real.log (1 + C^2 * γ^2 / Fintype.card (Fin k)) ≤ minimumOutputEntropy Φ by
    simpa only [Fintype.card_fin] using hresult
  apply minimumOutputEntropy_lower_of_self_pairing Φ C γ hC hγ
    (by simpa using hkR)
  intro ρ
  let X : HermitianMat (Fin k) ℂ := (Φ ρ).M - (k : ℝ)⁻¹ • 1
  have hXdiag : ∀ i, X i i = 0 := by
    intro i
    have hd := suppressor_output_diagonal H U hU Φ hΦ ρ i
    change (Φ ρ).m i i - ((k : ℝ)⁻¹ : ℝ) • (1 : Matrix (Fin k) (Fin k) ℂ) i i = 0
    simp [hd]
  have hXtr : X.trace = 0 := by
    simp [X, HermitianMat.trace_sub, HermitianMat.trace_smul,
      HermitianMat.trace_one, ne_of_gt hkR]
  have hself : inner ℝ (Φ ρ).M X = ‖X‖^2 := by
    have hx : (Φ ρ).M = X + (k : ℝ)⁻¹ • (1 : HermitianMat (Fin k) ℂ) := by
      dsimp [X]
      abel
    rw [hx]
    simp [inner_add_left, inner_smul_left, HermitianMat.one_inner, hXtr]
  let B : HermitianMat (Fin n) ℂ :=
    ⟨testObservable H U X, testObservable_isHermitian H hH U X⟩
  have hp := channelEntry_tracePairing (suppressorK H U) ρ.m X.mat
  have hm : Matrix.of (fun i j ↦ channelEntry (suppressorK H U) ρ.m i j) = (Φ ρ).m := by
    funext i j
    exact (hΦ ρ i j).symm
  rw [hm, suppressorK_zeroDiagonal_sum H U X.mat hXdiag] at hp
  have hpR := congrArg Complex.re hp
  have hp' : inner ℝ (Φ ρ).M X = inner ℝ ρ.M B / (k : ℝ) := by
    rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
    change ((Φ ρ).m * X.mat).trace.re =
      (ρ.m * testObservable H U X).trace.re / (k : ℝ)
    simpa only [Complex.div_natCast_re, HermitianMat.mat_apply, testObservable] using hpR
  have hpair : (k : ℝ) * ‖X‖^2 = inner ℝ ρ.M B := by
    rw [hself] at hp'
    exact (mul_comm _ _).trans ((eq_div_iff hkR.ne').mp hp')
  have hle := (state_inner_le_operatorNorm ρ B).trans (hbound X hXdiag)
  simpa only [Fintype.card_fin, X] using hpair.le.trans hle

#print axioms single_copy_lemma

end SuppressorEntropy
