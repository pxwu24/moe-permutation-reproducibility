import GapRemainder
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # Numerical parameters for the main theorem

The scalar estimates use exact rational arithmetic and certified logarithm
bounds. No floating-point assertion is used as a hypothesis.
-/

noncomputable section

namespace MainParameters

open EntropyGapRemainder

def M : ℕ := 2 ^ 27
def gamma : ℝ := 1 - 1 / 1000000
def error : ℝ := 1 / 1000000
def beta : ℝ := (10001 * gamma / 9999) ^ 2
def s0 : ℝ := gamma ^ 2 / (1 + error) ^ 2

def a (r : ℕ) : ℝ := 1 + beta * ((1 + 9 / (M : ℝ)) ^ r - 1)

theorem beta_bounds : 1 < beta ∧ beta < 1001 / 1000 := by
  norm_num [beta, gamma]

theorem signal_bounds :
    0 < s0 ∧ s0 < 1 ∧ 1 / (2 : ℝ) ^ 18 < 1 - s0 ∧
      1 - s0 < 4 / 1000000 := by
  norm_num [s0, gamma, error]

theorem log_M_bounds : 18711 / 1000 < Real.log (M : ℝ) ∧
    Real.log (M : ℝ) < 19 := by
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  simp only [M, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  constructor <;> norm_num at * <;> linarith

theorem log_signal_error_lower : -13 < Real.log (1 - s0) := by
  have h := Real.log_lt_log (by positivity : 0 < 1 / (2 : ℝ) ^ 18)
    signal_bounds.2.2.1
  rw [Real.log_div one_ne_zero (by norm_num), Real.log_one, Real.log_pow] at h
  have hhi := Real.log_two_lt_d9
  norm_num at h
  linarith

/-- A simple entropy bound: `-s log s ≤ 1-s`. -/
theorem binaryEntropy_le (s : ℝ) (hs : 0 < s) :
    binaryEntropy s ≤ (1 - s) * (1 - Real.log (1 - s)) := by
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hs) hs.le
  have hcancel : s * (1 - s⁻¹) = s - 1 := by
    field_simp [hs.ne']
  rw [hcancel] at h
  unfold binaryEntropy
  nlinarith

/-- The numerical margin is more than `5 × 10⁻⁹`. -/
theorem numerical_margin :
    (5 : ℝ) / 1000000000 <
      entropyDeficit (M : ℝ) s0 - 2 * Real.log (1 + 9 * beta / (M : ℝ)) := by
  have hs := signal_bounds
  have hlogs := log_M_bounds
  have hlogu := log_signal_error_lower
  have hbin := binaryEntropy_le s0 hs.1
  have hrem := (entropyDeficit_remainder_bounds (M : ℝ) s0
    (by norm_num [M]) hs.1 hs.2.1).1
  have hu : 0 < 1 - s0 := by linarith [hs.2.1]
  have hbin' : binaryEntropy s0 < 14 * (1 - s0) := by
    nlinarith [mul_pos hu (show 0 < 13 + Real.log (1 - s0) by linarith)]
  have hnum : 18710868 / 1000000 < s0 * Real.log (M : ℝ) - binaryEntropy s0 := by
    have hmul : (1 - s0) * Real.log (M : ℝ) < 19 * (1 - s0) :=
      by simpa only [mul_comm (1 - s0) (19 : ℝ)] using
        mul_lt_mul_of_pos_left hlogs.2 hu
    nlinarith [hs.2.2.2]
  have hb := beta_bounds
  have hp : 0 < 1 + 9 * beta / (M : ℝ) := by
    have : 0 < beta := lt_trans zero_lt_one hb.1
    positivity
  have hlog := Real.log_le_sub_one_of_pos hp
  norm_num [M] at hnum hrem hlog ⊢
  nlinarith [hb.2]

/-- Increasing a nonnegative coefficient to the outside of a power. -/
theorem affine_power_bound (b x : ℝ) (hb : 1 ≤ b) (hx : 0 ≤ x) (r : ℕ) :
    1 + b * ((1 + x) ^ r - 1) ≤ (1 + b * x) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hb0 : 0 ≤ b := by linarith
    have hx1 : 1 ≤ 1 + x := by linarith
    have hp : 1 ≤ (1 + x) ^ r := one_le_pow₀ hx1
    have hbase : 0 ≤ 1 + b * x := by positivity
    have hfactor : 0 ≤ b * (b - 1) * x * ((1 + x) ^ r - 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg hb0 (by linarith)) hx) (by linarith)
    calc
      1 + b * ((1 + x) ^ (r + 1) - 1) ≤
          (1 + b * x) * (1 + b * ((1 + x) ^ r - 1)) := by
        rw [pow_succ]
        nlinarith
      _ ≤ (1 + b * x) * (1 + b * x) ^ r :=
        mul_le_mul_of_nonneg_left ih hbase
      _ = (1 + b * x) ^ (r + 1) := by rw [pow_succ]; ring

theorem a_pos (r : ℕ) : 0 < a r := by
  have hp : 1 ≤ (1 + 9 / (M : ℝ)) ^ r := one_le_pow₀ (by norm_num [M])
  have hb : 0 ≤ beta := le_trans zero_le_one beta_bounds.1.le
  have hp0 : 0 ≤ (1 + 9 / (M : ℝ)) ^ r - 1 := sub_nonneg.mpr hp
  unfold a
  positivity

theorem a_le_power (r : ℕ) : a r ≤ (1 + 9 * beta / (M : ℝ)) ^ r := by
  have he : beta * (9 / (M : ℝ)) = 9 * beta / (M : ℝ) := by ring
  simpa only [a, he] using
    affine_power_bound beta (9 / (M : ℝ)) beta_bounds.1.le (by norm_num [M]) r

theorem log_a_le (r : ℕ) :
    Real.log (a r) ≤ (r : ℝ) * Real.log (1 + 9 * beta / (M : ℝ)) := by
  simpa only [Real.log_pow] using Real.log_le_log (a_pos r) (a_le_power r)

/-- A convenient uniform gap estimate using the fixed lower signal `s0`. -/
theorem fixed_signal_gap (r : ℕ) (hr : 0 < r) :
    (5 : ℝ) / 1000000000 * r <
      (r : ℝ) * entropyDeficit (M : ℝ) s0 - 2 * Real.log (a r) := by
  have h := mul_lt_mul_of_pos_left numerical_margin (by exact_mod_cast hr : (0 : ℝ) < r)
  have ha := log_a_le r
  nlinarith

/-- The explicit tensor exponent for a requested real threshold. -/
def rFor (N : ℝ) : ℕ := 100000000000 * ⌈N⌉₊

theorem log_large_constant : Real.log (100000000000 : ℝ) < 26 := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 100000000000)
    (by norm_num : (100000000000 : ℝ) < 2 ^ 37)
  rw [Real.log_pow] at h
  have hb := Real.log_two_lt_d9
  norm_num at h
  linarith

theorem log_randomizer_constant : 4 * Real.log (108 : ℝ) < 20 := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 108)
    (by norm_num : (108 : ℝ) < 2 ^ 7)
  rw [Real.log_pow] at h
  have hb := Real.log_two_lt_d9
  norm_num at h
  linarith

/-- The explicit choice of `r` makes the two-copy lower bound exceed `N`. -/
theorem final_two_copy_threshold (N : ℝ) (hN : 1 ≤ N) :
    N < (5 : ℝ) / 1000000000 * rFor N -
      8 * Real.log (rFor N : ℝ) - 4 * Real.log 108 := by
  let J : ℕ := ⌈N⌉₊
  have hNJ : N ≤ (J : ℝ) := Nat.le_ceil N
  have hJ : (1 : ℝ) ≤ J := hN.trans hNJ
  have hJ0 : (0 : ℝ) < J := lt_of_lt_of_le zero_lt_one hJ
  have hlogJ := Real.log_le_sub_one_of_pos hJ0
  have hlogr : Real.log (rFor N : ℝ) =
      Real.log (100000000000 : ℝ) + Real.log (J : ℝ) := by
    rw [rFor, Nat.cast_mul]
    exact Real.log_mul (by norm_num) hJ0.ne'
  rw [hlogr]
  have hr : (rFor N : ℝ) = 100000000000 * (J : ℝ) := by
    simp only [rFor, J, Nat.cast_mul, Nat.cast_ofNat]
  rw [hr]
  have hc := log_large_constant
  have hd := log_randomizer_constant
  nlinarith

/-- The explicit choice of `r` makes the one-copy upper bound less than `1/N`. -/
theorem final_one_copy_threshold (N : ℝ) (hN : 1 ≤ N) :
    Real.log (1 + 1 / (rFor N : ℝ) ^ 2) < 1 / N := by
  have hNJ : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
  have hJ : (1 : ℝ) ≤ ⌈N⌉₊ := hN.trans hNJ
  have hr : (rFor N : ℝ) = 100000000000 * (⌈N⌉₊ : ℝ) := by
    simp only [rFor, Nat.cast_mul, Nat.cast_ofNat]
  have hr0 : (0 : ℝ) < rFor N := by rw [hr]; positivity
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNr : N < (rFor N : ℝ) ^ 2 := by rw [hr]; nlinarith
  have hinv : 1 / (rFor N : ℝ) ^ 2 < 1 / N := by
    exact one_div_lt_one_div_of_lt hN0 hNr
  have hlog := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 1 + 1 / (rFor N : ℝ) ^ 2)
  linarith

/-- The chosen tensor exponent grows linearly with the requested threshold. -/
theorem rFor_bounds (N : ℝ) (hN : 1 ≤ N) :
    100000000000 * N ≤ (rFor N : ℝ) ∧
      (rFor N : ℝ) < 200000000000 * N := by
  have hlo : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
  have hhi : (⌈N⌉₊ : ℝ) < N + 1 := Nat.ceil_lt_add_one (by linarith)
  simp only [rFor, Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> nlinarith

/-- Rounding a logarithm upward selects a power of two within a factor two. -/
theorem power_two_ceil_log_bounds (x : ℝ) (hx : 1 ≤ x) :
    x ≤ (2 : ℝ) ^ ⌈Real.log x / Real.log 2⌉₊ ∧
      (2 : ℝ) ^ ⌈Real.log x / Real.log 2⌉₊ < 2 * x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlo := Nat.le_ceil (Real.log x / Real.log 2)
  have hhi := Nat.ceil_lt_add_one (div_nonneg hlog htwo.le)
  constructor
  · apply (Real.log_le_log_iff hx0 (by positivity)).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ htwo).mp hlo
  · apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow, Real.log_mul (by norm_num) hx0.ne']
    have hmul := mul_lt_mul_of_pos_right hhi htwo
    rw [add_mul, div_mul_cancel₀ _ htwo.ne', one_mul] at hmul
    linarith

def randomizerT (r : ℕ) : ℕ :=
  ⌈Real.log (54 * (r : ℝ) ^ 2 * Real.sqrt (a r)) / Real.log 2⌉₊

def randomizerH (r : ℕ) : ℕ := 2 ^ randomizerT r

def randomizerSize (r : ℕ) : ℕ := randomizerH r ^ 2

theorem one_le_a (r : ℕ) : 1 ≤ a r := by
  have hp : 1 ≤ (1 + 9 / (M : ℝ)) ^ r := one_le_pow₀ (by norm_num [M])
  have hb : 0 ≤ beta := le_trans zero_le_one beta_bounds.1.le
  have h := mul_nonneg hb (sub_nonneg.mpr hp)
  unfold a
  linarith

theorem randomizer_scale_gt_one (r : ℕ) (hr : 0 < r) :
    1 < 54 * (r : ℝ) ^ 2 * Real.sqrt (a r) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsq : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr1
  have ha : 1 ≤ Real.sqrt (a r) := Real.one_le_sqrt.mpr (one_le_a r)
  nlinarith

theorem randomizerT_pos (r : ℕ) (hr : 0 < r) : 0 < randomizerT r := by
  apply Nat.ceil_pos.mpr
  exact div_pos (Real.log_pos (randomizer_scale_gt_one r hr))
    (Real.log_pos (by norm_num))

theorem randomizerH_bounds (r : ℕ) (hr : 0 < r) :
    54 * (r : ℝ) ^ 2 * Real.sqrt (a r) ≤ (randomizerH r : ℝ) ∧
      (randomizerH r : ℝ) < 108 * (r : ℝ) ^ 2 * Real.sqrt (a r) := by
  have h := power_two_ceil_log_bounds
    (54 * (r : ℝ) ^ 2 * Real.sqrt (a r)) (randomizer_scale_gt_one r hr).le
  simp only [randomizerH, Nat.cast_pow, Nat.cast_ofNat, randomizerT]
  constructor
  · exact h.1
  · linarith [h.2]

theorem randomizerH_pos (r : ℕ) : 0 < randomizerH r := by
  unfold randomizerH
  positivity

theorem randomizerSize_bound (r : ℕ) (hr : 0 < r) :
    (randomizerSize r : ℝ) < 108 ^ 2 * (r : ℝ) ^ 4 * a r := by
  have hh0 : (0 : ℝ) ≤ randomizerH r := by positivity
  have hsq := mul_self_lt_mul_self hh0 (randomizerH_bounds r hr).2
  have hsqrt := Real.sq_sqrt (a_pos r).le
  have heq : (108 * (r : ℝ) ^ 2 * Real.sqrt (a r)) ^ 2 =
      108 ^ 2 * (r : ℝ) ^ 4 * a r := by
    rw [mul_pow, hsqrt]
    ring
  rw [← heq]
  simpa only [randomizerSize, Nat.cast_pow, pow_two, Nat.cast_mul] using hsq

/-- The polynomial root bound yields the required contraction coefficient. -/
theorem randomizer_contraction_bound (r : ℕ) (hr : 0 < r) :
    (54 * (r : ℝ) - 1) / (randomizerH r : ℝ) <
      1 / ((r : ℝ) * Real.sqrt (a r)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have ha0 : 0 < Real.sqrt (a r) := Real.sqrt_pos.2 (a_pos r)
  have hh0 : (0 : ℝ) < randomizerH r := by exact_mod_cast randomizerH_pos r
  apply (div_lt_div_iff₀ hh0 (mul_pos hr0 ha0)).mpr
  have hlo := (randomizerH_bounds r hr).1
  nlinarith [mul_pos hr0 ha0]

/-- The entropy cost of the two independent output randomizations. -/
theorem log_randomizerSize_bound (r : ℕ) (hr : 0 < r) :
    Real.log (randomizerSize r : ℝ) <
      2 * Real.log 108 + 4 * Real.log (r : ℝ) + Real.log (a r) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hell : (0 : ℝ) < randomizerSize r := by
    unfold randomizerSize
    exact_mod_cast pow_pos (randomizerH_pos r) 2
  have h := Real.log_lt_log hell (randomizerSize_bound r hr)
  rw [Real.log_mul (by positivity) (a_pos r).ne',
    Real.log_mul (by norm_num) (pow_pos hr0 4).ne', Real.log_pow, Real.log_pow] at h
  norm_num at h
  exact h

/-- The numerical two-copy bound after the explicit output randomization. -/
theorem smoothed_two_copy_gap (r : ℕ) (hr : 0 < r) :
    (5 : ℝ) / 1000000000 * r - 8 * Real.log (r : ℝ) - 4 * Real.log 108 <
      (r : ℝ) * entropyDeficit (M : ℝ) s0 -
        2 * Real.log (randomizerSize r : ℝ) := by
  have hgap := fixed_signal_gap r hr
  have hsize := log_randomizerSize_bound r hr
  linarith

theorem rFor_pos (N : ℝ) (hN : 1 ≤ N) : 0 < rFor N := by
  have h := (rFor_bounds N hN).1
  have : (0 : ℝ) < rFor N := by nlinarith
  exact_mod_cast this

/-- Explicit exponential bounds for the output dimension. -/
theorem output_dimension_bounds (N : ℝ) (hN : 1 ≤ N) :
    Real.exp (100000000000 * Real.log (M : ℝ) * N) ≤ (M : ℝ) ^ rFor N ∧
      (M : ℝ) ^ rFor N < Real.exp (200000000000 * Real.log (M : ℝ) * N) := by
  have hM0 : (0 : ℝ) < M := by norm_num [M]
  have hlogM : 0 < Real.log (M : ℝ) := by linarith [log_M_bounds.1]
  have hpow : (M : ℝ) ^ rFor N = Real.exp ((rFor N : ℝ) * Real.log (M : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hM0]
  rw [hpow]
  have hb := rFor_bounds N hN
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hb.1 hlogM.le]
  · apply Real.exp_lt_exp.mpr
    nlinarith [mul_lt_mul_of_pos_right hb.2 hlogM]

end MainParameters
