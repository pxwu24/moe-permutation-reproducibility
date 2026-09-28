import MainFilterParameters
import MainParameters

/-! Explicit coarse dimension bounds for the exact parameter choices. -/
noncomputable section
namespace MainDimensions
open MainFilterParameters

lemma k_large (r : ℕ) (hr : 1 ≤ r) : (134217728 : ℝ) ≤ k r := by
  have h := le_self_pow₀ (show 1 ≤ M by norm_num) (by omega : r ≠ 0)
  exact_mod_cast h

lemma r_le_k (r : ℕ) : (r : ℝ) ≤ k r := by
  have h₁ : r < 2 ^ r := Nat.lt_two_pow_self
  have h₂ : 2 ^ r ≤ k r := by
    unfold k
    exact Nat.pow_le_pow_left (by norm_num) r
  exact_mod_cast (le_trans h₁.le h₂)

lemma log_k (r : ℕ) : Real.log (k r : ℝ) = (r : ℝ) * Real.log (M : ℝ) := by
  simp [k, Real.log_pow]

lemma log_theta_bounds : 1 / 10000 ≤ 2 * Real.log θ ∧ 2 * Real.log θ < 1 := by
  have hlo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < θ)
  have hhi := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < θ)
  norm_num [θ] at hlo hhi ⊢
  constructor <;> linarith

lemma gridBase_bounds (r : ℕ) :
    (2 : ℝ) ≤ 2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ) ∧
      2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ) ≤ 30002 * (k r : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k r := by exact_mod_cast k_ge_one r
  have hspos : 0 < Real.sqrt C₁ * k r := by
    have hk0 : (0 : ℝ) < k r := by exact_mod_cast k_pos r
    positivity
  have hceil : 0 < Nat.ceil (Real.sqrt C₁ * k r) := Nat.ceil_pos.mpr hspos
  have hceilR : (1 : ℝ) ≤ Nat.ceil (Real.sqrt C₁ * k r) := by exact_mod_cast hceil
  have hup := Nat.ceil_lt_add_one hspos.le
  have hsqrt : Real.sqrt C₁ < 15000 := by
    have hsq : (Real.sqrt C₁) ^ 2 = 200000000 := Real.sq_sqrt (by norm_num)
    have hnon := Real.sqrt_nonneg C₁
    nlinarith
  have hmul := mul_lt_mul_of_pos_right hsqrt (by exact_mod_cast k_pos r : (0 : ℝ) < k r)
  constructor <;> nlinarith

lemma log_P_bounds (r : ℕ) (hr : 1 ≤ r) :
    (k r : ℝ) ≤ Real.log (P r : ℝ) ∧
      Real.log (P r : ℝ) ≤ 30002 * (k r : ℝ) ^ 3 := by
  have hk := k_large r hr
  have hk1 := k_ge_one r
  have hb := gridBase_bounds r
  have hb0 : 0 < 2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ) := by linarith
  have hloglo : (1 / 2 : ℝ) ≤ Real.log (2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ)) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hb.1
    have hn := Real.log_two_gt_d9
    linarith
  have hloghi := (Real.log_le_self hb0.le).trans hb.2
  have heq : Real.log (P r : ℝ) =
      ((k r : ℝ) * ((k r : ℝ) - 1)) *
        Real.log (2 * (Nat.ceil (Real.sqrt C₁ * k r) : ℝ)) := by
    simp only [P, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_sub hk1,
      Nat.cast_one, Nat.cast_ofNat]
  rw [heq]
  have hexp : 0 ≤ (k r : ℝ) * ((k r : ℝ) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  constructor
  · have h := mul_le_mul_of_nonneg_left hloglo hexp
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hloghi hexp
    nlinarith

lemma log_numerator_bounds (r : ℕ) (hr : 1 ≤ r) :
    (k r : ℝ) ≤ Real.log (2 * (P r : ℝ) / E) ∧
      Real.log (2 * (P r : ℝ) / E) ≤ (k r : ℝ) ^ 4 := by
  have hk := k_large r hr
  have hp0 : (0 : ℝ) < P r := by exact_mod_cast (lt_of_lt_of_le (by decide) (P_ge_one r))
  have hp := log_P_bounds r hr
  have heq : Real.log (2 * (P r : ℝ) / E) =
      Real.log 2000000 + Real.log (P r : ℝ) := by
    rw [show 2 * (P r : ℝ) / E = 2000000 * (P r : ℝ) by unfold E; ring]
    exact Real.log_mul (by norm_num) hp0.ne'
  rw [heq]
  have hc0 : 0 ≤ Real.log (2000000 : ℝ) := Real.log_nonneg (by norm_num)
  have hc1 : Real.log (2000000 : ℝ) ≤ 2000000 := Real.log_le_self (by norm_num)
  constructor
  · linarith
  · have hk3 : (1 : ℝ) ≤ (k r : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    have hprod : 0 ≤ ((k r : ℝ) - 2030002) * (k r : ℝ) ^ 3 :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith

lemma L_bounds (r : ℕ) (hr : 1 ≤ r) :
    (k r : ℝ) ≤ L r ∧ (L r : ℝ) ≤ (k r : ℝ) ^ 5 := by
  have hk := k_large r hr
  have hn := log_numerator_bounds r hr
  have ht := log_theta_bounds
  have hd : 0 < 2 * Real.log θ := by linarith
  have hn0 : 0 ≤ Real.log (2 * (P r : ℝ) / E) := by linarith
  have hlo := Nat.le_ceil (Real.log (2 * (P r : ℝ) / E) / (2 * Real.log θ))
  have hhi := Nat.ceil_lt_add_one (div_nonneg hn0 hd.le)
  change (k r : ℝ) ≤ ↑⌈Real.log (2 * (P r : ℝ) / E) / (2 * Real.log θ)⌉₊ ∧
    (⌈Real.log (2 * (P r : ℝ) / E) / (2 * Real.log θ)⌉₊ : ℝ) ≤ (k r : ℝ) ^ 5
  constructor
  · have hdiv : (k r : ℝ) ≤ Real.log (2 * (P r : ℝ) / E) / (2 * Real.log θ) := by
      apply (le_div_iff₀ hd).mpr
      nlinarith
    exact hdiv.trans hlo
  · have hdiv : Real.log (2 * (P r : ℝ) / E) / (2 * Real.log θ) ≤ 10000 * (k r : ℝ) ^ 4 := by
      apply (div_le_iff₀ hd).mpr
      have hm := mul_le_mul_of_nonneg_right ht.1 (show 0 ≤ 10000 * (k r : ℝ) ^ 4 by positivity)
      nlinarith
    have hk4 : (1 : ℝ) ≤ (k r : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    have hm : 0 ≤ ((k r : ℝ) - 10001) * (k r : ℝ) ^ 4 :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith

lemma q_bounds (r : ℕ) (hr : 1 ≤ r) :
    (k r : ℝ) ≤ q r ∧ (q r : ℝ) ≤ (k r : ℝ) ^ 7 := by
  have hk := k_large r hr
  have hL := L_bounds r hr
  have hlog2lo : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log (2 : ℝ) < 1 := by linarith [Real.log_two_lt_d9]
  have hlogb0 : Real.log (2 : ℝ) ≤ Real.log (4 * M - 1 : ℕ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlogb1 : Real.log (4 * M - 1 : ℕ) ≤ 4 * (k r : ℝ) := by
    have h := Real.log_le_self (by positivity : (0 : ℝ) ≤ (4 * M - 1 : ℕ))
    norm_num [M] at h ⊢
    linarith
  have hlogk0 : 0 ≤ Real.log (k r : ℝ) := Real.log_nonneg (by linarith)
  have hlogk1 := Real.log_le_self (by positivity : (0 : ℝ) ≤ k r)
  let f := 4 * (Real.log (4 * M - 1 : ℕ) / Real.log 2) +
    2 * (Real.log (k r : ℝ) / Real.log 2)
  have hf0 : 1 ≤ f := by
    have h : (1 : ℝ) ≤ Real.log (4 * M - 1 : ℕ) / Real.log 2 :=
      (le_div_iff₀ (show 0 < Real.log 2 by linarith)).mpr (by simpa using hlogb0)
    have h' := div_nonneg hlogk0 (show 0 ≤ Real.log 2 by linarith)
    dsimp [f]
    nlinarith
  have hf1 : f ≤ 36 * (k r : ℝ) := by
    have hb : Real.log (4 * M - 1 : ℕ) / Real.log 2 ≤ 8 * (k r : ℝ) := by
      apply (div_le_iff₀ (show 0 < Real.log 2 by linarith)).mpr
      nlinarith
    have hk' : Real.log (k r : ℝ) / Real.log 2 ≤ 2 * (k r : ℝ) := by
      apply (div_le_iff₀ (show 0 < Real.log 2 by linarith)).mpr
      nlinarith
    dsimp [f]
    linarith
  have hL0 : (0 : ℝ) ≤ L r := Nat.cast_nonneg _
  have hlo := Nat.le_ceil ((L r : ℝ) * f)
  have hhi := Nat.ceil_lt_add_one (mul_nonneg hL0 (by linarith : 0 ≤ f))
  have heq : (q r : ℝ) = 2 + (⌈(L r : ℝ) * f⌉₊ : ℝ) := by
    simp only [q, f, Nat.cast_add, Nat.cast_ofNat]
  rw [heq]
  constructor
  · nlinarith [mul_nonneg hL0 (show 0 ≤ f - 1 by linarith)]
  · have hm := mul_le_mul hf1 hL.2 hL0 (show 0 ≤ 36 * (k r : ℝ) by positivity)
    have hk6 : (1 : ℝ) ≤ (k r : ℝ) ^ 6 := one_le_pow₀ (by linarith)
    have hprod : 0 ≤ ((k r : ℝ) - 39) * (k r : ℝ) ^ 6 :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith

/-- The input dimension after adjoining the Weyl label. -/
def inputDimension (r : ℕ) : ℕ := k r ^ 2 * Q r ^ (2 * r)

lemma inputDimension_pos (r : ℕ) : 0 < inputDimension r := by
  unfold inputDimension Q
  exact mul_pos (pow_pos (k_pos r) _) (by positivity)

lemma log_inputDimension (r : ℕ) :
    Real.log (inputDimension r : ℝ) =
      2 * Real.log (k r : ℝ) + 2 * (r : ℝ) * q r * Real.log 2 := by
  have hk : (0 : ℝ) < k r := by exact_mod_cast k_pos r
  simp only [inputDimension, Q, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  ring

lemma log_inputDimension_bounds (r : ℕ) (hr : 1 ≤ r) :
    (k r : ℝ) ≤ Real.log (inputDimension r : ℝ) ∧
      Real.log (inputDimension r : ℝ) ≤ (k r : ℝ) ^ 10 := by
  have hk := k_large r hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hq := q_bounds r hr
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlogk0 : 0 ≤ Real.log (k r : ℝ) := Real.log_nonneg (by linarith)
  have hlogk1 := Real.log_le_self (by positivity : (0 : ℝ) ≤ k r)
  rw [log_inputDimension]
  constructor
  · have hfactor : 1 ≤ 2 * (r : ℝ) * Real.log 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg (q r) : (0 : ℝ) ≤ q r)
    nlinarith
  · have hprod := mul_le_mul (r_le_k r) hq.2
      (Nat.cast_nonneg (q r) : (0 : ℝ) ≤ q r) (Nat.cast_nonneg (k r) : (0 : ℝ) ≤ k r)
    have hlogmul := mul_le_mul_of_nonneg_left hlog2hi
      (show (0 : ℝ) ≤ 2 * r * q r by positivity)
    have hpow1 : (k r : ℝ) ≤ (k r : ℝ) ^ 8 := by
      simpa only [pow_one] using pow_le_pow_right₀ (show (1 : ℝ) ≤ k r by linarith)
        (show 1 ≤ 8 by omega)
    have hpow2 : 4 ≤ (k r : ℝ) ^ 2 := by nlinarith
    have hpow3 := mul_le_mul_of_nonneg_right hpow2 (show (0 : ℝ) ≤ (k r : ℝ) ^ 8 by positivity)
    nlinarith

/-- Uniform, explicit doubly exponential bounds in the tensor parameter. -/
theorem input_dimension_double_exp (r : ℕ) (hr : 1 ≤ r) :
    Real.exp (Real.exp (r : ℝ)) ≤ (inputDimension r : ℝ) ∧
      (inputDimension r : ℝ) ≤ Real.exp (Real.exp (200 * (r : ℝ))) := by
  have hn : (0 : ℝ) < inputDimension r := by exact_mod_cast inputDimension_pos r
  have hk : (0 : ℝ) < k r := by exact_mod_cast k_pos r
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hmlo : (1 : ℝ) < Real.log (M : ℝ) := by
    have h := MainParameters.log_M_bounds.1
    norm_num [MainParameters.M, M] at h ⊢
    linarith
  have hmhi : Real.log (M : ℝ) < 19 := by
    simpa [MainParameters.M, M] using MainParameters.log_M_bounds.2
  have hlo : Real.exp (r : ℝ) ≤ k r := by
    calc
      Real.exp (r : ℝ) ≤ Real.exp ((r : ℝ) * Real.log (M : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = k r := by rw [← log_k, Real.exp_log hk]
  have hhi : (k r : ℝ) ^ 10 ≤ Real.exp (200 * (r : ℝ)) := by
    calc
      (k r : ℝ) ^ 10 = Real.exp (Real.log ((k r : ℝ) ^ 10)) :=
        (Real.exp_log (pow_pos hk 10)).symm
      _ ≤ Real.exp (200 * (r : ℝ)) := by
        apply Real.exp_le_exp.mpr
        rw [Real.log_pow, log_k]
        norm_num
        norm_num [M] at hmhi
        nlinarith
  have hb := log_inputDimension_bounds r hr
  constructor
  · calc
      Real.exp (Real.exp (r : ℝ)) ≤ Real.exp (Real.log (inputDimension r : ℝ)) :=
        Real.exp_le_exp.mpr (hlo.trans hb.1)
      _ = _ := Real.exp_log hn
  · calc
      (inputDimension r : ℝ) = Real.exp (Real.log (inputDimension r : ℝ)) :=
        (Real.exp_log hn).symm
      _ ≤ Real.exp (Real.exp (200 * (r : ℝ))) :=
        Real.exp_le_exp.mpr (hb.2.trans hhi)

/-- The final input dimensions are doubly exponential in the requested gain. -/
theorem final_input_dimension_bounds (N : ℝ) (hN : 1 ≤ N) :
    Real.exp (Real.exp (100000000000 * N)) ≤
        (inputDimension (MainParameters.rFor N) : ℝ) ∧
      (inputDimension (MainParameters.rFor N) : ℝ) ≤
        Real.exp (Real.exp (40000000000000 * N)) := by
  have hr := MainParameters.rFor_bounds N hN
  have hb := input_dimension_double_exp (MainParameters.rFor N)
    (MainParameters.rFor_pos N hN)
  constructor
  · exact (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hr.1)).trans hb.1
  · apply hb.2.trans
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    nlinarith [hr.2]

end MainDimensions
