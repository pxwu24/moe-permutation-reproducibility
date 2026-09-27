import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# A. Tensor calibration arithmetic

The tensor-scale normalization converts the single-channel entropy parameter
into the normalized difference of powers appearing in the tensor construction.
-/

noncomputable section

namespace TensorCalibration

/-- The square-root scale of the difference between the tensor dimensions. -/
def tensorScale (M r : ℕ) : ℝ :=
  Real.sqrt (((M : ℝ) + 9) ^ r - (M : ℝ) ^ r)

/-- The tensor calibration scale is strictly positive in the nontrivial range. -/
lemma scale_pos (M r : ℕ) (hM : 2 ≤ M) (hr : 1 ≤ r) :
    0 < tensorScale M r := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  apply Real.sqrt_pos.mpr
  apply sub_pos.mpr
  exact pow_lt_pow_left₀ (by norm_num : (M : ℝ) < (M : ℝ) + 9)
    hM0.le (by omega)

/-- Squaring the tensor scale recovers its difference of powers. -/
lemma scale_sq (M r : ℕ) (hM : 2 ≤ M) (hr : 1 ≤ r) :
    tensorScale M r ^ 2 = ((M : ℝ) + 9) ^ r - (M : ℝ) ^ r := by
  exact Real.sq_sqrt (Real.sqrt_pos.mp (scale_pos M r hM hr)).le

/-- Dividing the squared tensor scale by the input dimension normalizes the power. -/
lemma normalized_scale_sq (M r : ℕ) (hM : 2 ≤ M) (hr : 1 ≤ r) :
    tensorScale M r ^ 2 / (M : ℝ) ^ r = (1 + 9 / (M : ℝ)) ^ r - 1 := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [scale_sq M r hM hr, sub_div, div_self (pow_ne_zero r hMne),
    ← div_pow, add_div, div_self hMne]

/-- The calibrated entropy coefficient has the normalized tensor-power form. -/
lemma calibrated_single_entropy_normalization (M r : ℕ) (hM : 2 ≤ M)
    (hr : 1 ≤ r) (c C1 C2 γ : ℝ) (hC1 : 2 < C1)
    (hC2 : C2 = c * (Real.sqrt C1 - Real.sqrt 2) * tensorScale M r) :
    (C2 / (Real.sqrt C1 - Real.sqrt 2)) ^ 2 * γ ^ 2 / (M ^ r : ℕ) =
      γ ^ 2 * c ^ 2 * ((1 + 9 / (M : ℝ)) ^ r - 1) := by
  have hdiff : Real.sqrt C1 - Real.sqrt 2 ≠ 0 :=
    (sub_pos.mpr (Real.sqrt_lt_sqrt (by norm_num) hC1)).ne'
  have hcancel : C2 / (Real.sqrt C1 - Real.sqrt 2) = c * tensorScale M r := by
    rw [hC2]
    field_simp
  rw [hcancel, mul_pow, Nat.cast_pow]
  calc
    c ^ 2 * tensorScale M r ^ 2 * γ ^ 2 / (M : ℝ) ^ r =
        γ ^ 2 * c ^ 2 * (tensorScale M r ^ 2 / (M : ℝ) ^ r) := by ring
    _ = γ ^ 2 * c ^ 2 * ((1 + 9 / (M : ℝ)) ^ r - 1) := by
      rw [normalized_scale_sq M r hM hr]

/-- A strict margin in the scalar calibration remains strict after tensor scaling. -/
lemma calibrated_margin (M r : ℕ) (hM : 2 ≤ M) (hr : 1 ≤ r)
    (c C1 : ℝ) (hC1 : 2 < C1)
    (hmargin : 1 < c * (Real.sqrt C1 - Real.sqrt 2) / Real.sqrt C1) :
    Real.sqrt C1 * tensorScale M r <
      c * (Real.sqrt C1 - Real.sqrt 2) * tensorScale M r := by
  have hroot : 0 < Real.sqrt C1 := Real.sqrt_pos.mpr (by linarith)
  have hscalar : Real.sqrt C1 < c * (Real.sqrt C1 - Real.sqrt 2) := by
    simpa using (lt_div_iff₀ hroot).mp hmargin
  exact mul_lt_mul_of_pos_right hscalar (scale_pos M r hM hr)

/-- The user's square-root margin is exactly the calibration ratio margin. -/
lemma user_margin_iff_ratio (c C1 : ℝ) (hC1 : 2 < C1) :
    1 < c * (1 - Real.sqrt (2 / C1)) ↔
      1 < c * (Real.sqrt C1 - Real.sqrt 2) / Real.sqrt C1 := by
  have hroot : Real.sqrt C1 ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have heq : c * (1 - Real.sqrt (2 / C1)) =
      c * (Real.sqrt C1 - Real.sqrt 2) / Real.sqrt C1 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  rw [heq]

/-- A nontrivial base and positive tensor exponent give a nontrivial dimension. -/
lemma two_le_pow (M r : ℕ) (hM : 2 ≤ M) (hr : 1 ≤ r) : 2 ≤ M ^ r := by
  exact hM.trans (le_self_pow₀ (by omega) (by omega))

#print axioms scale_pos
#print axioms scale_sq
#print axioms normalized_scale_sq
#print axioms calibrated_single_entropy_normalization
#print axioms calibrated_margin
#print axioms user_margin_iff_ratio
#print axioms two_le_pow

end TensorCalibration
