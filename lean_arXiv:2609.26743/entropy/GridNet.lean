import QuantumInfo.ForMathlib.HermitianMat.Inner
import Mathlib.Algebra.Order.Round

/-! Gaussian-integer rounding on the zero-diagonal Hermitian Hilbert space.
The resulting grid is exactly the grid used for the finite spectral filter. -/
noncomputable section
open scoped BigOperators

namespace GaussianHermitianGrid

def gaussianRound (z : ℂ) : ℂ :=
  ⟨(round z.re : ℝ), (round z.im : ℝ)⟩

lemma gaussianRound_gaussian (z : ℂ) :
    ∃ p q : ℤ, gaussianRound z = (p : ℂ) + (q : ℂ) * Complex.I := by
  refine ⟨round z.re, round z.im, ?_⟩
  apply Complex.ext <;> simp [gaussianRound]

lemma gaussianRound_error (z : ℂ) : ‖z - gaussianRound z‖ ^ 2 ≤ 1/2 := by
  have hr : (z.re - (round z.re : ℝ)) ^ 2 ≤ (1/2 : ℝ)^2 := by
    nlinarith [sq_le_sq₀ (abs_nonneg (z.re - (round z.re : ℝ)))
      (show (0 : ℝ) ≤ 1/2 by norm_num) |>.mpr (abs_sub_round z.re),
      sq_abs (z.re - (round z.re : ℝ))]
  have hi : (z.im - (round z.im : ℝ)) ^ 2 ≤ (1/2 : ℝ)^2 := by
    nlinarith [sq_le_sq₀ (abs_nonneg (z.im - (round z.im : ℝ)))
      (show (0 : ℝ) ≤ 1/2 by norm_num) |>.mpr (abs_sub_round z.im),
      sq_abs (z.im - (round z.im : ℝ))]
  rw [Complex.sq_norm, Complex.normSq_apply]
  change (z.re - (round z.re : ℝ)) * (z.re - (round z.re : ℝ)) +
    (z.im - (round z.im : ℝ)) * (z.im - (round z.im : ℝ)) ≤ 1/2
  nlinarith

variable {k : ℕ}

def roundedMatrix (X : HermitianMat (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => if i < j then gaussianRound (X i j)
    else if j < i then star (gaussianRound (X j i)) else 0

lemma roundedMatrix_hermitian (X : HermitianMat (Fin k) ℂ) :
    (roundedMatrix X).IsHermitian := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [Matrix.conjTranspose_apply, roundedMatrix, hij, not_lt_of_gt hij]
  · subst j
    simp [Matrix.conjTranspose_apply, roundedMatrix]
  · simp [Matrix.conjTranspose_apply, roundedMatrix, hij, not_lt_of_gt hij]

def rounded (X : HermitianMat (Fin k) ℂ) : HermitianMat (Fin k) ℂ :=
  ⟨roundedMatrix X, roundedMatrix_hermitian X⟩

lemma rounded_diag (X : HermitianMat (Fin k) ℂ) (i : Fin k) : rounded X i i = 0 := by
  change roundedMatrix X i i = 0
  simp [roundedMatrix]

lemma rounded_gaussian (X : HermitianMat (Fin k) ℂ) (i j : Fin k) :
    ∃ p q : ℤ, rounded X i j = (p : ℂ) + (q : ℂ) * Complex.I := by
  change ∃ p q : ℤ, roundedMatrix X i j = (p : ℂ) + (q : ℂ) * Complex.I
  rcases lt_trichotomy i j with hij | hij | hij
  · simpa [roundedMatrix, hij] using gaussianRound_gaussian (X i j)
  · subst j
    exact ⟨0, 0, by simp [roundedMatrix]⟩
  · obtain ⟨p,q,hpq⟩ := gaussianRound_gaussian (X j i)
    refine ⟨p, -q, ?_⟩
    simp [roundedMatrix, hij, not_lt_of_gt hij, hpq]

lemma rounded_entry_error (X : HermitianMat (Fin k) ℂ)
    (hdiag : ∀ i, X i i = 0) (i j : Fin k) :
    ‖X i j - rounded X i j‖ ^ 2 ≤ 1/2 := by
  change ‖X i j - roundedMatrix X i j‖ ^ 2 ≤ 1/2
  rcases lt_trichotomy i j with hij | hij | hij
  · simpa [roundedMatrix, hij] using gaussianRound_error (X i j)
  · subst j
    simp [roundedMatrix, hdiag]
  · have hx : X i j = star (X j i) := by
      exact (congrFun (congrFun X.H i) j).symm
    rw [roundedMatrix, if_neg (not_lt_of_gt hij), if_pos hij, hx, ← star_sub]
    rw [norm_star]
    exact gaussianRound_error (X j i)

lemma rounded_error (X : HermitianMat (Fin k) ℂ) (hdiag : ∀ i, X i i = 0) :
    ‖X - rounded X‖ ≤ (k : ℝ) * Real.sqrt 2 / 2 := by
  rw [HermitianMat.norm_eq_frobenius, ← Real.sqrt_eq_rpow]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hs : (∑ i : Fin k, ∑ j : Fin k, ‖(X - rounded X) i j‖ ^ 2) ≤
      (k : ℝ)^2 / 2 := by
    calc
      _ ≤ ∑ _i : Fin k, ∑ _j : Fin k, (1/2 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact rounded_entry_error X hdiag i j
      _ = (k : ℝ)^2 / 2 := by simp; ring
  have ht : ((k : ℝ) * Real.sqrt 2 / 2)^2 = (k : ℝ)^2 / 2 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [sq_nonneg ((k : ℝ) * Real.sqrt 2)]
  exact ht ▸ hs

/-- Membership in the exact nonzero Gaussian-integer grid, expressed in the
Hilbert--Schmidt norm (equivalently `Tr W²`). -/
def InGrid (C₁ : ℝ) (W : HermitianMat (Fin k) ℂ) : Prop :=
  (∀ i, W i i = 0) ∧
  (∀ i j, ∃ p q : ℤ, W i j = (p : ℂ) + (q : ℂ) * Complex.I) ∧
  0 < ‖W‖ ^ 2 ∧ ‖W‖ ^ 2 ≤ C₁ * (k : ℝ)^2

/-- Shrink and round a unit Hilbert--Schmidt vector. The normalized integer
point lies in the closed unit ball and is within `√2/√C₁` of the original
vector. In particular the grid point is nonzero when `C₁ > 2`. -/
theorem grid_net (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (X : HermitianMat (Fin k) ℂ) (hdiag : ∀ i, X i i = 0) (hX : ‖X‖ = 1) :
    ∃ W : HermitianMat (Fin k) ℂ, InGrid C₁ W ∧
      ‖((Real.sqrt C₁ * (k : ℝ))⁻¹ : ℝ) • W‖ ≤ 1 ∧
      ‖X - ((Real.sqrt C₁ * (k : ℝ))⁻¹ : ℝ) • W‖ ≤
        Real.sqrt 2 / Real.sqrt C₁ := by
  let a := Real.sqrt C₁
  let b := a * (k : ℝ)
  let e := (k : ℝ) * Real.sqrt 2 / 2
  let t := b - e
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hk)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2a : Real.sqrt 2 < a := Real.sqrt_lt_sqrt (by norm_num) hC₁
  have hb : 0 < b := mul_pos ha hkpos
  have he : 0 ≤ e := by positivity
  have he_le_b : e ≤ b := by
    have hh := mul_le_mul_of_nonneg_left (le_of_lt hs2a) hkpos.le
    dsimp [e, b]
    nlinarith [mul_nonneg hkpos.le hs2.le]
  have ht : 0 ≤ t := sub_nonneg.mpr he_le_b
  let Y := t • X
  let W := rounded Y
  have hYdiag : ∀ i, Y i i = 0 := by
    intro i
    change t • X i i = 0
    rw [hdiag, smul_zero]
  have herr : ‖Y-W‖ ≤ e := rounded_error Y hYdiag
  have hYn : ‖Y‖ = t := by simp [Y, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hX]
  have hWn : ‖W‖ ≤ b := by
    calc
      ‖W‖ ≤ ‖Y‖ + ‖Y-W‖ := by
        simpa only [norm_sub_rev] using (norm_le_insert' W Y)
      _ ≤ t + e := add_le_add (le_of_eq hYn) herr
      _ = b := by dsimp [t]; ring
  have hdist : ‖b • X - W‖ ≤ 2 * e := by
    have heq : b • X - Y = e • X := by
      dsimp [Y, t]
      rw [← sub_smul]
      congr 1
      ring
    calc
      ‖b • X - W‖ ≤ ‖b • X-Y‖ + ‖Y-W‖ := by
        simpa only [dist_eq_norm] using dist_triangle (b • X) Y W
      _ ≤ e + e := by
        apply add_le_add _ herr
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg he, hX, mul_one]
      _ = 2*e := by ring
  have hinv : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  have hnW : ‖b⁻¹ • W‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
    calc b⁻¹ * ‖W‖ ≤ b⁻¹ * b := mul_le_mul_of_nonneg_left hWn hinv
      _ = 1 := inv_mul_cancel₀ hb.ne'
  have hclose : ‖X - b⁻¹ • W‖ ≤ Real.sqrt 2 / a := by
    have heq : X - b⁻¹ • W = b⁻¹ • (b • X-W) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
    calc
      b⁻¹ * ‖b • X-W‖ ≤ b⁻¹ * (2*e) := mul_le_mul_of_nonneg_left hdist hinv
      _ = Real.sqrt 2 / a := by dsimp [b, e]; field_simp
  have hdelta : Real.sqrt 2 / a < 1 := (div_lt_one ha).mpr hs2a
  have hWne : W ≠ 0 := by
    intro hz
    rw [hz, smul_zero, sub_zero, hX] at hclose
    linarith
  have hWsq : ‖W‖^2 ≤ C₁ * (k : ℝ)^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg W) hb.le).mpr hWn
    have ha2 : a^2 = C₁ := Real.sq_sqrt (by linarith)
    simpa only [b, mul_pow, ha2] using hh
  refine ⟨W, ⟨rounded_diag Y, rounded_gaussian Y, ?_, hWsq⟩, hnW, hclose⟩
  exact sq_pos_of_pos (norm_pos_iff.mpr hWne)

lemma trace_square_eq_norm_sq (W : HermitianMat (Fin k) ℂ) :
    (W ^ 2).trace = ‖W‖ ^ 2 := by
  have hh := congrArg Complex.re (HermitianMat.norm_eq_trace_sq W)
  change (W.mat ^ 2).trace.re = ‖W‖^2
  have hcast : (((‖W‖ : ℝ) : ℂ)^2).re = ‖W‖^2 := by norm_cast
  exact hh.symm.trans hcast

theorem grid_net_trace (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (X : HermitianMat (Fin k) ℂ) (hdiag : ∀ i, X i i = 0) (hX : ‖X‖ = 1) :
    ∃ W : HermitianMat (Fin k) ℂ,
      (∀ i, W i i = 0) ∧
      (∀ i j, ∃ p q : ℤ, W i j = (p : ℂ) + (q : ℂ) * Complex.I) ∧
      0 < (W ^ 2).trace ∧ (W ^ 2).trace ≤ C₁ * (k : ℝ)^2 ∧
      ‖((Real.sqrt C₁ * (k : ℝ))⁻¹ : ℝ) • W‖ ≤ 1 ∧
      ‖X - ((Real.sqrt C₁ * (k : ℝ))⁻¹ : ℝ) • W‖ ≤
        Real.sqrt 2 / Real.sqrt C₁ := by
  obtain ⟨W,hW,hn,hclose⟩ := grid_net C₁ hC₁ hk X hdiag hX
  refine ⟨W,hW.1,hW.2.1,?_,?_,hn,hclose⟩
  · simpa only [trace_square_eq_norm_sq] using hW.2.2.1
  · simpa only [trace_square_eq_norm_sq] using hW.2.2.2

#print axioms rounded_error
#print axioms grid_net
#print axioms grid_net_trace

end GaussianHermitianGrid
