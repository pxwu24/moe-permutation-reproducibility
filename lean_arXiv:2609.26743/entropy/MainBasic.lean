import MainReal
import SupplementSingle
import SupplementEntropy

/-! # A. Bounds for the constructed full-grid quantum channel -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open ComplexOrder EntropyLemmas.BellAlgebra SuppressorEntropy
open ActualGridSupport ActualGridFilterLower MainChannel ActualTensorBasis

namespace MainBasic

variable {n k : ℕ}

lemma single_copy (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (hC₂ : 0 < C₂)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (L : ℕ) (hL : 1 ≤ L) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (ρ : MState (Fin n)) :
    (k : ℝ) *
        ‖(fullGridChannel C₁ hC₁ hk C₂ U hU L γ hγ hγ1 ρ).M -
          (k : ℝ)⁻¹ • (1 : HermitianMat (Fin k) ℂ)‖ ^ 2 ≤
      (C₂ / (Real.sqrt C₁ - Real.sqrt 2)) ^ 2 * γ ^ 2 / k := by
  have hd : 0 < Real.sqrt C₁ - Real.sqrt 2 :=
    sub_pos.mpr (Real.sqrt_lt_sqrt (by norm_num) hC₁)
  let Φ := fullGridChannel C₁ hC₁ hk C₂ U hU L γ hγ hγ1
  have hb : ∀ W : HermitianMat (Fin k) ℂ, (∀ i, W i i = 0) →
      ‖testObservable (fullGridH C₁ hC₁ hk C₂ U L γ).mat U W‖ ≤
        (C₂ / (Real.sqrt C₁ - Real.sqrt 2)) * γ * ‖W‖ := by
    intro W hW
    have h := actual_grid_support_bound C₁ C₂ hC₁ hC₂ hk U L hL γ hγ W hW
    change ‖testObservable (fullGridH C₁ hC₁ hk C₂ U L γ).mat U W‖ ≤
      C₂ * γ / (Real.sqrt C₁ - Real.sqrt 2) * ‖W‖ at h
    convert h using 1
    ring
  have h := SupplementSingle.single_copy_hilbertSchmidt_bound
    (fullGridH C₁ hC₁ hk C₂ U L γ).mat (fullGridH C₁ hC₁ hk C₂ U L γ).H
    U hU Φ (fun ρ i j => fullGridChannel_entry C₁ hC₁ hk C₂ U hU L γ hγ hγ1 ρ.m i j)
    (C₂ / (Real.sqrt C₁ - Real.sqrt 2)) γ (div_nonneg hC₂.le hd.le) hγ
    (by omega) hb ρ
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  calc
    _ ≤ (k : ℝ) * ((C₂ / (Real.sqrt C₁ - Real.sqrt 2)) ^ 2 * γ ^ 2 / (k : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left h hkR.le
    _ = _ := by field_simp

lemma two_copy {d : Type*} [Fintype d] [DecidableEq d]
    {M r : ℕ} [Nonempty (Fin n)]
    (hn : 0 < n) (hM : 2 ≤ M) (hr : 1 ≤ r)
    (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ)
    (hT : ∀ i, (T i).conjTranspose * T i = 1)
    (hreal : ∀ i, (T i).map star = T i)
    (C₁ : ℝ) (hC₁ : 2 < C₁) (C₂ : ℝ) (L : ℕ)
    (γ ε : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (htrace : (fullGridFilter C₁ hC₁ (TensorCalibration.two_le_pow M r hM hr)
      C₂ (enumeratedTuple e T) L).mat.trace.re ≤ n * ε) :
    let U := enumeratedTuple e T
    let Φ := fullGridChannel C₁ hC₁ (TensorCalibration.two_le_pow M r hM hr)
      C₂ U (enumeratedTuple_unitary e T hT) L γ hγ.le hγ1.le
    Sᵥₙ ((Φ.prod Φ) (MState.pure (Ket.MES (Fin n)))) ≤
      (r : ℝ) * referenceEntropy M γ ε := by
  dsimp only
  let hk := TensorCalibration.two_le_pow M r hM hr
  let U := enumeratedTuple e T
  let F := fullGridFilter C₁ hC₁ hk C₂ U L
  let H := fullGridH C₁ hC₁ hk C₂ U L γ
  let Φ := fullGridChannel C₁ hC₁ hk C₂ U (enumeratedTuple_unitary e T hT)
    L γ hγ.le hγ1.le
  have hsq : H.mat * H.mat = (γ : ℂ) • (1 + F.mat)⁻¹ := by
    have h := congrArg HermitianMat.mat
      (ActualGridFilterProperties.fullGridH_sq C₁ hC₁ hk C₂ U L γ hγ.le)
    ext i j
    simpa only [H, F, HermitianMat.mat_pow, pow_two, HermitianMat.mat_smul,
      HermitianMat.mat_inv, HermitianMat.mat_add, HermitianMat.mat_one,
      Matrix.smul_apply, smul_eq_mul, Complex.real_smul] using congrFun₂ h i j
  have hUr (i) : (U i).transpose = (U i).conjTranspose := by
    have h := congrArg Matrix.transpose (enumeratedTuple_real e T hreal i)
    exact h.symm
  exact (SupplementEntropy.corollary1 hn hM e T hT F.mat H.mat
    (HermitianMat.zero_le_iff.mp
      (ActualGridFilterProperties.fullGridFilter_nonneg C₁ hC₁ hk C₂ U L))
    H.H γ ε hγ hγ1 hε hsq htrace Φ Φ
    (fullGridChannel_entry C₁ hC₁ hk C₂ U (enumeratedTuple_unitary e T hT)
      L γ hγ.le hγ1.le)
    (MainReal.fullGridChannel_real C₁ hC₁ hk C₂ U (enumeratedTuple_unitary e T hT)
      hUr L γ hγ.le hγ1.le)).2

#print axioms single_copy
#print axioms two_copy

end MainBasic
