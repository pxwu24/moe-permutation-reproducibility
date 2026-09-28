import ActualGridSupport

/-!
# A. Positivity and normalization of the actual suppressing operator

These results establish the algebraic hypotheses needed to turn the actual
finite-grid construction into a quantum channel and apply the two-copy lemma.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open ComplexOrder

namespace ActualGridFilterProperties

variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-- The actual finite-grid filter is positive semidefinite. -/
lemma fullGridFilter_nonneg (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ) (L : ℕ) :
    0 ≤ ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L := by
  let : Fintype (ActualGridSupport.GridIndex C₁ k) :=
    (GaussianHermitianGrid.grid_finite C₁ (by linarith) (by omega)).fintype
  exact FiniteFilterSupport.filter_nonneg (ActualGridSupport.gridObservable C₁ C₂ U) L

/-- The full-grid suppressing operator is positive semidefinite. -/
lemma fullGridH_nonneg (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ) (L : ℕ) (γ : ℝ) :
    0 ≤ ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ := by
  exact smul_nonneg (Real.sqrt_nonneg γ) (HermitianMat.sqrt_nonneg _)

/-- The defining identity `H² = γ (I+F)⁻¹` for the actual finite-grid filter. -/
lemma fullGridH_sq (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ) (L : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ ^ 2 =
      γ • (1 + ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L)⁻¹ := by
  let F := ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L
  have hp : (1 + F).mat.PosDef := by
    simpa using Matrix.PosDef.one.add_posSemidef
      (HermitianMat.zero_le_iff.mp (fullGridFilter_nonneg C₁ hC₁ hk C₂ U L))
  have hi : 0 ≤ (1 + F)⁻¹ := HermitianMat.zero_le_iff.mpr hp.inv.posSemidef
  apply HermitianMat.ext
  change (Real.sqrt γ • (1 + F)⁻¹.sqrt.mat) ^ 2 = γ • (1 + F)⁻¹.mat
  rw [smul_pow, Real.sq_sqrt hγ, pow_two, HermitianMat.sqrt_sq hi]

/-- The resolvent of `I+F` is a positive contraction. -/
lemma fullGridFilter_inv_le_one (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ) (L : ℕ) :
    (1 + ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L)⁻¹ ≤
      (1 : HermitianMat d ℂ) := by
  let F := ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L
  have hp : (1 + F).mat.PosDef := by
    simpa using Matrix.PosDef.one.add_posSemidef
      (HermitianMat.zero_le_iff.mp (fullGridFilter_nonneg C₁ hC₁ hk C₂ U L))
  have hi : 0 ≤ (1 + F)⁻¹ := HermitianMat.zero_le_iff.mpr hp.inv.posSemidef
  have horder : (1 : HermitianMat d ℂ) ≤ 1 + F := by
    simpa using add_le_add_left (fullGridFilter_nonneg C₁ hC₁ hk C₂ U L) 1
  have hc := HermitianMat.conj_mono (M := (1 + F)⁻¹.sqrt.mat) horder
  have he1 : (1 : HermitianMat d ℂ).conj (1 + F)⁻¹.sqrt.mat = (1 + F)⁻¹ := by
    apply HermitianMat.ext
    simp only [HermitianMat.conj_apply_mat, HermitianMat.mat_one,
      Matrix.mul_one, HermitianMat.conjTranspose_mat]
    exact HermitianMat.sqrt_sq hi
  have he2 : (1 + F).conj (1 + F)⁻¹.sqrt.mat = 1 := by
    apply HermitianMat.ext
    simpa only [HermitianMat.conj_apply_mat, HermitianMat.mat_one,
      HermitianMat.conjTranspose_mat] using
        HermitianMat.sqrt_inv_mul_self_mul_sqrt_inv_eq_one hp
  rwa [he1, he2] at hc

/-- The squared suppressing operator is bounded by `γ I`. -/
lemma fullGridH_sq_le_gamma (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ) (L : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ ^ 2 ≤
      γ • (1 : HermitianMat d ℂ) := by
  rw [fullGridH_sq C₁ hC₁ hk C₂ U L γ hγ]
  exact smul_le_smul_of_nonneg_left (fullGridFilter_inv_le_one C₁ hC₁ hk C₂ U L) hγ

/-- The actual suppressing operator satisfies the channel normalization hypothesis. -/
lemma fullGridH_sq_le_one (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ) (L : ℕ) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ ^ 2 ≤
      (1 : HermitianMat d ℂ) := by
  apply (fullGridH_sq_le_gamma C₁ hC₁ hk C₂ U L γ hγ).trans
  simpa only [one_smul] using
    smul_le_smul_of_nonneg_right hγ1
      (show (0 : HermitianMat d ℂ) ≤ 1 from
        HermitianMat.zero_le_iff.mpr Matrix.PosSemidef.one)

#print axioms fullGridFilter_nonneg
#print axioms fullGridH_nonneg
#print axioms fullGridH_sq
#print axioms fullGridFilter_inv_le_one
#print axioms fullGridH_sq_le_gamma
#print axioms fullGridH_sq_le_one

end ActualGridFilterProperties
