import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace EntropyGapRemainder

def logMerge (x y : ℝ) : ℝ :=
  (x + y) * Real.log (x + y) - x * Real.log x - y * Real.log y

theorem logMerge_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    logMerge x y =
      x * Real.log ((x + y) / x) + y * Real.log ((x + y) / y) := by
  rw [Real.log_div (ne_of_gt (add_pos hx hy)) (ne_of_gt hx),
    Real.log_div (ne_of_gt (add_pos hx hy)) (ne_of_gt hy)]
  unfold logMerge
  ring

theorem logMerge_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ logMerge x y := by
  rw [logMerge_eq x y hx hy]
  apply add_nonneg
  · apply mul_nonneg hx.le
    apply Real.log_nonneg
    apply (le_div_iff₀ hx).2
    linarith
  · apply mul_nonneg hy.le
    apply Real.log_nonneg
    apply (le_div_iff₀ hy).2
    linarith

theorem logMerge_le (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y ≤ 1) :
    logMerge x y ≤ y * (1 - Real.log y) := by
  have hfirst : x * Real.log ((x + y) / x) ≤ y := by
    calc
      x * Real.log ((x + y) / x) ≤ x * ((x + y) / x - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos (add_pos hx hy) hx)) hx.le
      _ = y := by field_simp; ring
  have hsecond : y * Real.log ((x + y) / y) ≤ -y * Real.log y := by
    calc
      y * Real.log ((x + y) / y) ≤ y * Real.log (1 / y) := by
        apply mul_le_mul_of_nonneg_left _ hy.le
        apply Real.log_le_log (div_pos (add_pos hx hy) hy)
        exact div_le_div_of_nonneg_right hxy hy.le
      _ = -y * Real.log y := by
        rw [Real.log_div one_ne_zero (ne_of_gt hy), Real.log_one]
        ring
  rw [logMerge_eq x y hx hy]
  nlinarith

def binaryEntropy (s : ℝ) : ℝ :=
  -s * Real.log s - (1 - s) * Real.log (1 - s)

def entropyDeficit (k s : ℝ) : ℝ :=
  ((1 + (k - 1) * s) * Real.log (1 + (k - 1) * s) +
    (k - 1) * (1 - s) * Real.log (1 - s)) / k ^ 2

theorem entropyDeficit_remainder_eq (k s : ℝ) (hk : 0 < k)
    (hs : 0 < s) (hs1 : s < 1) :
    entropyDeficit k s - (s * Real.log k - binaryEntropy s) / k =
      logMerge s ((1 - s) / k) / k := by
  have hb : 0 < 1 - s := sub_pos.mpr hs1
  have hd : 0 < (1 - s) / k := div_pos hb hk
  have ha : 1 + (k - 1) * s = k * (s + (1 - s) / k) := by
    field_simp
    ring
  have hlog : Real.log (1 + (k - 1) * s) =
      Real.log k + Real.log (s + (1 - s) / k) := by
    rw [ha, Real.log_mul (ne_of_gt hk) (ne_of_gt (add_pos hs hd))]
  unfold entropyDeficit binaryEntropy logMerge
  rw [hlog, Real.log_div (ne_of_gt hb) (ne_of_gt hk)]
  field_simp
  ring

theorem entropyDeficit_remainder_bounds (k s : ℝ) (hk : 1 ≤ k)
    (hs : 0 < s) (hs1 : s < 1) :
    0 ≤ entropyDeficit k s - (s * Real.log k - binaryEntropy s) / k ∧
    entropyDeficit k s - (s * Real.log k - binaryEntropy s) / k ≤
      (1 - s) / k ^ 2 * (Real.log k + 1 - Real.log (1 - s)) := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hb : 0 < 1 - s := sub_pos.mpr hs1
  have hd : 0 < (1 - s) / k := div_pos hb hk0
  have hds : s + (1 - s) / k ≤ 1 := by
    have : (1 - s) / k ≤ 1 - s := by
      apply (div_le_iff₀ hk0).2
      nlinarith
    linarith
  rw [entropyDeficit_remainder_eq k s hk0 hs hs1]
  constructor
  · exact div_nonneg (logMerge_nonneg s ((1 - s) / k) hs hd) hk0.le
  · calc
      logMerge s ((1 - s) / k) / k ≤
          (((1 - s) / k) * (1 - Real.log ((1 - s) / k))) / k :=
        div_le_div_of_nonneg_right (logMerge_le s ((1 - s) / k) hs hd hds) hk0.le
      _ = (1 - s) / k ^ 2 * (Real.log k + 1 - Real.log (1 - s)) := by
        rw [Real.log_div (ne_of_gt hb) (ne_of_gt hk0)]
        field_simp
        ring

#print axioms entropyDeficit_remainder_eq
#print axioms entropyDeficit_remainder_bounds

end EntropyGapRemainder
