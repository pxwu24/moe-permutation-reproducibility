import MainDimensions
import Mathlib.Analysis.Asymptotics.Defs

/-! Quantitative bounds proving every growth rate in the parameter table. -/
noncomputable section
namespace MainParameterGrowth
open MainFilterParameters Filter Asymptotics

lemma log_M : Real.log (M : ℝ) = 27 * Real.log 2 := by
  rw [show (M : ℝ) = (2 : ℝ) ^ 27 by norm_num, Real.log_pow]
  norm_num

lemma log_M_bounds : 1 ≤ Real.log (M : ℝ) ∧ Real.log (M : ℝ) ≤ 27 := by
  rw [log_M]
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  constructor <;> linarith

lemma scale_pos (r : ℕ) (hr : 1 ≤ r) : 1 ≤ (r : ℝ) * (k r : ℝ) ^ 2 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk : (1 : ℝ) ≤ (k r : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast k_ge_one r)
  nlinarith

lemma log_gridBase_bounds (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) ≤ Real.log (2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ)) ∧
      Real.log (2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ)) ≤ 30029 * r := by
  have hk : (0 : ℝ) < k r := by exact_mod_cast k_pos r
  have hs : (1 : ℝ) ≤ Real.sqrt C₁ := by
    nlinarith [Real.sqrt_nonneg C₁, Real.sq_sqrt (show 0 ≤ C₁ by norm_num)]
  have hceil := Nat.le_ceil (Real.sqrt C₁ * k r)
  have hkbase : (k r : ℝ) ≤ 2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ Real.sqrt C₁ - 1 by linarith) hk.le]
  have hbase := MainDimensions.gridBase_bounds r
  have hlo := Real.log_le_log hk hkbase
  have hhi := Real.log_le_log (by linarith : 0 < 2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ)) hbase.2
  rw [Real.log_mul (by norm_num) hk.ne', MainDimensions.log_k] at hhi
  rw [MainDimensions.log_k] at hlo
  have hc := Real.log_le_self (show (0 : ℝ) ≤ 30002 by norm_num)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hM := log_M_bounds
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by positivity) (show 0 ≤ Real.log (M : ℝ) - 1 by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by positivity) (show 0 ≤ 27 - Real.log (M : ℝ) by linarith)]

/-- The logarithm of the exact Gaussian-grid cardinality bound. -/
lemma log_P_bounds (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) * (k r : ℝ) ^ 2 / 2 ≤ Real.log (P r : ℝ) ∧
      Real.log (P r : ℝ) ≤ 30029 * ((r : ℝ) * (k r : ℝ) ^ 2) := by
  have hk := MainDimensions.k_large r hr
  have hb := log_gridBase_bounds r hr
  have hrR : (0 : ℝ) ≤ r := by positivity
  have heq : Real.log (P r : ℝ) =
      ((k r : ℝ) * ((k r : ℝ) - 1)) *
        Real.log (2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ)) := by
    simp only [P, Nat.cast_pow, Real.log_pow, Nat.cast_mul,
      Nat.cast_sub (k_ge_one r), Nat.cast_one, Nat.cast_ofNat]
  have ha0 : 0 ≤ (k r : ℝ) * ((k r : ℝ) - 1) := mul_nonneg (by positivity) (by linarith)
  have ha1 : (k r : ℝ) ^ 2 / 2 ≤ (k r : ℝ) * ((k r : ℝ) - 1) := by nlinarith
  have ha2 : (k r : ℝ) * ((k r : ℝ) - 1) ≤ (k r : ℝ) ^ 2 := by nlinarith
  rw [heq]
  constructor
  · have h := mul_le_mul ha1 hb.1 hrR ha0
    nlinarith
  · have h := mul_le_mul ha2 hb.2 (by linarith : 0 ≤ Real.log (2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ))) (sq_nonneg (k r : ℝ))
    nlinarith

/-- Ceiling and logarithmic denominator change the growth by fixed constants only. -/
lemma L_bounds (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) * (k r : ℝ) ^ 2 / 2 ≤ L r ∧
      (L r : ℝ) ≤ 30000000000 * ((r : ℝ) * (k r : ℝ) ^ 2) := by
  have hscale := scale_pos r hr
  have hp := log_P_bounds r hr
  have ht := MainDimensions.log_theta_bounds
  have hd : 0 < 2 * Real.log θ := by linarith
  have hp0 : (0 : ℝ) < P r := by exact_mod_cast (lt_of_lt_of_le (by decide) (P_ge_one r))
  have heq : Real.log (2 * (P r : ℝ) / E) = Real.log 2000000 + Real.log (P r : ℝ) := by
    rw [show 2 * (P r : ℝ) / E = 2000000 * (P r : ℝ) by unfold E; ring]
    exact Real.log_mul (by norm_num) hp0.ne'
  have hc0 : 0 ≤ Real.log (2000000 : ℝ) := Real.log_nonneg (by norm_num)
  have hc1 := Real.log_le_self (show (0 : ℝ) ≤ 2000000 by norm_num)
  have hx0 : 0 ≤ Real.log (2 * (P r : ℝ) / E) := by rw [heq]; linarith
  have hlo := Nat.le_ceil (Real.log (2 * (P r : ℝ) / E) / (2 * Real.log θ))
  have hhi := Nat.ceil_lt_add_one (div_nonneg hx0 hd.le)
  unfold L
  constructor
  · have hdiv : (r : ℝ) * (k r : ℝ) ^ 2 / 2 ≤ Real.log (2 * (P r : ℝ) / E) / (2 * Real.log θ) := by
      apply (le_div_iff₀ hd).2
      rw [heq]
      nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) * (k r : ℝ) ^ 2 / 2 by positivity)
        (show 0 ≤ 1 - 2 * Real.log θ by linarith)]
    exact hdiv.trans hlo
  · have hdiv : Real.log (2 * (P r : ℝ) / E) / (2 * Real.log θ) ≤
        29999999999 * ((r : ℝ) * (k r : ℝ) ^ 2) := by
      apply (div_le_iff₀ hd).2
      rw [heq]
      have hh := mul_le_mul_of_nonneg_right ht.1
        (show 0 ≤ 29999999999 * ((r : ℝ) * (k r : ℝ) ^ 2) by positivity)
      nlinarith
    linarith

lemma q_factor_bounds (r : ℕ) (hr : 1 ≤ r) :
    54 * (r : ℝ) ≤ 4 * (Real.log (4 * M - 1 : ℕ) / Real.log 2) +
      2 * (Real.log (k r : ℝ) / Real.log 2) ∧
    4 * (Real.log (4 * M - 1 : ℕ) / Real.log 2) +
      2 * (Real.log (k r : ℝ) / Real.log 2) ≤ 170 * (r : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hb0 : 0 ≤ Real.log (4 * M - 1 : ℕ) := Real.log_nonneg (by norm_num)
  have hb : Real.log (4 * M - 1 : ℕ) ≤ 29 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < (4 * M - 1 : ℕ))
      (by norm_num : ((4 * M - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 29)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hb' : Real.log (4 * M - 1 : ℕ) / Real.log 2 ≤ 29 := (div_le_iff₀ hlog2).2 hb
  have hk : Real.log (k r : ℝ) / Real.log 2 = 27 * r := by
    rw [MainDimensions.log_k, log_M]
    field_simp
  rw [hk]
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hb'' := div_nonneg hb0 hlog2.le
  constructor <;> nlinarith

lemma q_bounds (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) ^ 2 * (k r : ℝ) ^ 2 ≤ q r ∧
      (q r : ℝ) ≤ 6000000000000 * ((r : ℝ) ^ 2 * (k r : ℝ) ^ 2) := by
  have hl := L_bounds r hr
  have hf := q_factor_bounds r hr
  have hs := scale_pos r hr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  let f := 4 * (Real.log (4 * M - 1 : ℕ) / Real.log 2) +
    2 * (Real.log (k r : ℝ) / Real.log 2)
  have hf0 : 0 ≤ f := by dsimp [f]; linarith
  have hlo := Nat.le_ceil ((L r : ℝ) * f)
  have hhi := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg (L r)) hf0)
  have heq : (q r : ℝ) = 2 + (⌈(L r : ℝ) * f⌉₊ : ℝ) := by simp [q, f]
  have hmullo := mul_le_mul hl.1 hf.1 (by positivity : 0 ≤ 54 * (r : ℝ)) (Nat.cast_nonneg (L r))
  have hmulhi := mul_le_mul hl.2 hf.2 hf0 (by positivity : 0 ≤ 30000000000 * ((r : ℝ) * (k r : ℝ) ^ 2))
  change _ * _ ≤ (L r : ℝ) * f at hmullo
  change (L r : ℝ) * f ≤ _ * _ at hmulhi
  have hscale : 1 ≤ (r : ℝ) ^ 2 * (k r : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) - 1 by linarith) (show 0 ≤ (r : ℝ) * (k r : ℝ) ^ 2 by positivity)]
  rw [heq]
  constructor <;> nlinarith

lemma log_input_bounds (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) ^ 3 * (k r : ℝ) ^ 2 ≤ Real.log (MainDimensions.inputDimension r : ℝ) ∧
      Real.log (MainDimensions.inputDimension r : ℝ) ≤
        20000000000000 * ((r : ℝ) ^ 3 * (k r : ℝ) ^ 2) := by
  have hq := q_bounds r hr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk1 : (1 : ℝ) ≤ (k r : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast k_ge_one r)
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlogk0 : 0 ≤ Real.log (k r : ℝ) := Real.log_nonneg (by exact_mod_cast k_ge_one r)
  have hlogk1 : Real.log (k r : ℝ) ≤ 27 * r := by
    rw [MainDimensions.log_k]
    nlinarith [mul_le_mul_of_nonneg_left log_M_bounds.2 (show 0 ≤ (r : ℝ) by positivity)]
  have hmlo := mul_le_mul_of_nonneg_left hq.1 (show 0 ≤ (r : ℝ) by positivity)
  have hmhi := mul_le_mul_of_nonneg_left hq.2 (show 0 ≤ (r : ℝ) by positivity)
  have hhlo := mul_le_mul_of_nonneg_left hlog2lo (show 0 ≤ 2 * (r : ℝ) * q r by positivity)
  have hhhi := mul_le_mul_of_nonneg_left hlog2hi (show 0 ≤ 2 * (r : ℝ) * q r by positivity)
  have hs : 1 ≤ (r : ℝ) ^ 2 * (k r : ℝ) ^ 2 := by nlinarith
  have hsr := mul_le_mul_of_nonneg_left hs (show 0 ≤ (r : ℝ) by positivity)
  rw [MainDimensions.log_inputDimension]
  constructor <;> nlinarith

lemma A_comparison (r : ℕ) (hr : 1 ≤ r) :
    ((M : ℝ) + 9) ^ r ≤ 20000000 * A r ∧ A r ≤ ((M : ℝ) + 9) ^ r := by
  constructor
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
    have hpow : (M : ℝ) ^ s ≤ ((M : ℝ) + 9) ^ s :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) s
    have hB : (0 : ℝ) ≤ (134217737 : ℝ) ^ s := by positivity
    simp only [A, pow_add, pow_one]
    norm_num [M] at hpow ⊢
    nlinarith
  · unfold A
    have hpow : 0 ≤ (M : ℝ) ^ r := by positivity
    linarith

lemma C₂_bounds (r : ℕ) (hr : 1 ≤ r) :
    Real.sqrt (((M : ℝ) + 9) ^ r) ≤ C₂ r ∧
      C₂ r ≤ 20000 * Real.sqrt (((M : ℝ) + 9) ^ r) := by
  have hA : 0 ≤ A r := le_trans (by norm_num) (A_ge_one r hr)
  have hAB := A_comparison r hr
  have hC0 : 0 ≤ C₂ r := by unfold C₂; positivity
  have hCsq : (C₂ r) ^ 2 = 200040002 * A r := by
    unfold C₂
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hA]
    norm_num
  have hBsqrt0 := Real.sqrt_nonneg (((M : ℝ) + 9) ^ r)
  have hBsqrt := Real.sq_sqrt (show 0 ≤ ((M : ℝ) + 9) ^ r by positivity)
  constructor
  · nlinarith
  · have hcoef : 10001 * Real.sqrt (2 : ℝ) ≤ 20000 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    have hsqrt := Real.sqrt_le_sqrt hAB.2
    unfold C₂
    have h := mul_le_mul hcoef hsqrt (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 20000)
    exact h

lemma k_sq (r : ℕ) : (k r : ℝ) ^ 2 = (M : ℝ) ^ (2 * r) := by
  simp only [k, Nat.cast_pow, ← pow_mul, Nat.mul_comm]

/-- A convenient positive-function form of the definition of Θ. -/
lemma theta_of_bounds (f g : ℕ → ℝ) (C : ℝ)
    (h : ∀ r, 1 ≤ r → 0 ≤ g r ∧ g r ≤ 2 * f r ∧ f r ≤ C * g r) :
    f =Θ[atTop] g := by
  constructor
  · apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with r hr
    obtain ⟨hg, hlo, hhi⟩ := h r hr
    have hf : 0 ≤ f r := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg] using hhi
  · apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with r hr
    obtain ⟨hg, hlo, hhi⟩ := h r hr
    have hf : 0 ≤ f r := by linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg] using hlo

/-- The exact cardinality factor satisfies the growth rate used in Table II. -/
theorem log_P_theta :
    (fun r : ℕ => Real.log (P r : ℝ)) =Θ[atTop]
      (fun r : ℕ => (r : ℝ) * (M : ℝ) ^ (2 * r)) := by
  apply theta_of_bounds _ _ 30029
  intro r hr
  rw [← k_sq]
  have h := log_P_bounds r hr
  exact ⟨by positivity, by linarith, h.2⟩

theorem L_theta :
    (fun r : ℕ => (L r : ℝ)) =Θ[atTop]
      (fun r : ℕ => (r : ℝ) * (M : ℝ) ^ (2 * r)) := by
  apply theta_of_bounds _ _ 30000000000
  intro r hr
  rw [← k_sq]
  have h := L_bounds r hr
  exact ⟨by positivity, by linarith, h.2⟩

theorem q_theta :
    (fun r : ℕ => (q r : ℝ)) =Θ[atTop]
      (fun r : ℕ => (r : ℝ) ^ 2 * (M : ℝ) ^ (2 * r)) := by
  apply theta_of_bounds _ _ 6000000000000
  intro r hr
  rw [← k_sq]
  have h := q_bounds r hr
  exact ⟨by positivity, by linarith [Nat.cast_nonneg (q r) (α := ℝ)], h.2⟩

/-- Equivalently, Q_r = exp(Θ(r² M^(2r))). -/
theorem log_Q_theta :
    (fun r : ℕ => Real.log (Q r : ℝ)) =Θ[atTop]
      (fun r : ℕ => (r : ℝ) ^ 2 * (M : ℝ) ^ (2 * r)) := by
  apply theta_of_bounds _ _ 6000000000000
  intro r hr
  rw [← k_sq]
  have h := q_bounds r hr
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlo := mul_le_mul_of_nonneg_left hlog2lo (Nat.cast_nonneg (q r) : (0 : ℝ) ≤ q r)
  have hhi := mul_le_mul_of_nonneg_left hlog2hi (Nat.cast_nonneg (q r) : (0 : ℝ) ≤ q r)
  simp only [Q, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  exact ⟨by positivity, by nlinarith, by nlinarith⟩

/-- Equivalently, n_r = exp(Θ(r³ M^(2r))). -/
theorem log_inputDimension_theta :
    (fun r : ℕ => Real.log (MainDimensions.inputDimension r : ℝ)) =Θ[atTop]
      (fun r : ℕ => (r : ℝ) ^ 3 * (M : ℝ) ^ (2 * r)) := by
  apply theta_of_bounds _ _ 20000000000000
  intro r hr
  rw [← k_sq]
  have h := log_input_bounds r hr
  refine ⟨by positivity, ?_, h.2⟩
  have hg : 0 ≤ (r : ℝ) ^ 3 * (k r : ℝ) ^ 2 := by positivity
  linarith

/-- C₂ has the square-root exponential growth in the table. -/
theorem C₂_theta_sqrt :
    (fun r : ℕ => C₂ r) =Θ[atTop]
      (fun r : ℕ => Real.sqrt (((M : ℝ) + 9) ^ r)) := by
  apply theta_of_bounds _ _ 20000
  intro r hr
  have h := C₂_bounds r hr
  refine ⟨Real.sqrt_nonneg _, ?_, h.2⟩
  have hg := Real.sqrt_nonneg (((M : ℝ) + 9) ^ r)
  linarith

/-- The output dimension is exp(Θ(r)). -/
theorem log_outputDimension_theta :
    (fun r : ℕ => Real.log (k r : ℝ)) =Θ[atTop] (fun r : ℕ => (r : ℝ)) := by
  apply theta_of_bounds _ _ 27
  intro r hr
  rw [MainDimensions.log_k]
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hm := log_M_bounds
  have hlo := mul_le_mul_of_nonneg_left hm.1 hr0
  have hhi := mul_le_mul_of_nonneg_left hm.2 hr0
  exact ⟨hr0, by nlinarith, by nlinarith⟩

lemma sqrt_power (r : ℕ) :
    Real.sqrt (((M : ℝ) + 9) ^ r) = ((M : ℝ) + 9) ^ ((r : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((M : ℝ) + 9) r,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (M : ℝ) + 9)]
  congr 1
  ring

/-- Exactly the C₂ row, using the real half-power notation of the paper. -/
theorem C₂_theta :
    (fun r : ℕ => C₂ r) =Θ[atTop]
      (fun r : ℕ => ((M : ℝ) + 9) ^ ((r : ℝ) / 2)) := by
  simpa only [sqrt_power] using C₂_theta_sqrt

end MainParameterGrowth
