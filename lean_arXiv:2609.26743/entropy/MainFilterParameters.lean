import AdderTrace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The concrete parameters used in the main theorem.  This file proves that
these parameters meet every hypothesis of the adder trace estimate and that
the actual full-grid filter has normalized trace less than 10⁻⁶.
-/

noncomputable section
namespace MainFilterParameters

open AdderTrace

abbrev M : ℕ := 134217728
abbrev C₁ : ℝ := 200000000
abbrev E : ℝ := 1 / 1000000
abbrev θ : ℝ := 10001 / 10000

def k (r : ℕ) : ℕ := M ^ r
def A (r : ℕ) : ℝ := ((M : ℝ) + 9) ^ r - (M : ℝ) ^ r
def C₂ (r : ℕ) : ℝ := 10001 * Real.sqrt 2 * Real.sqrt (A r)
def P (r : ℕ) : ℕ :=
  (2 * Nat.ceil (Real.sqrt C₁ * k r)) ^ (k r * (k r - 1))
def L (r : ℕ) : ℕ := Nat.ceil (Real.log (2 * (P r : ℝ) / E) / (2 * Real.log θ))
def q (r : ℕ) : ℕ := 2 + Nat.ceil
  ((L r : ℝ) * (4 * (Real.log (4 * M - 1 : ℕ) / Real.log 2) +
    2 * (Real.log (k r) / Real.log 2)))
def Q (r : ℕ) : ℕ := 2 ^ q r

lemma k_pos (r : ℕ) : 0 < k r := by unfold k; positivity
lemma k_ge_one (r : ℕ) : 1 ≤ k r := k_pos r

lemma A_ge_one (r : ℕ) (hr : 1 ≤ r) : 1 ≤ A r := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold A
  have hpow : (M : ℝ) ^ s ≤ ((M : ℝ) + 9) ^ s := by
    apply pow_le_pow_left₀ <;> norm_num
  have hlarge : (1 : ℝ) ≤ ((M : ℝ) + 9) ^ s := one_le_pow₀ (by norm_num)
  simp only [pow_add, pow_one]
  nlinarith

lemma P_ge_one (r : ℕ) : 1 ≤ P r := by
  unfold P
  apply one_le_pow₀
  have hs : (0 : ℝ) < Real.sqrt C₁ * k r := mul_pos (Real.sqrt_pos.2 (by norm_num))
    (by exact_mod_cast k_pos r)
  have hc : 0 < Nat.ceil (Real.sqrt C₁ * k r) := Nat.ceil_pos.2 hs
  omega

lemma sqrt_C₁ : Real.sqrt C₁ = 10000 * Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
    Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg C₁,
    Real.sq_sqrt (show (0 : ℝ) ≤ C₁ by norm_num)]

lemma C₂_eq (r : ℕ) : C₂ r = θ * Real.sqrt C₁ * delta M r := by
  rw [sqrt_C₁]
  unfold C₂ θ delta A
  ring

lemma C₂_large (r : ℕ) (hr : 1 ≤ r) : Real.sqrt C₁ * delta M r < C₂ r := by
  rw [C₂_eq]
  have hd : 0 < delta M r := Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num) (A_ge_one r hr))
  have hs : 0 < Real.sqrt C₁ := Real.sqrt_pos.2 (by norm_num)
  have ht : 1 < θ := by norm_num
  have h := mul_lt_mul_of_pos_right ht (mul_pos hs hd)
  nlinarith

/-- The logarithmic ceiling gives both a positive moment order and its decay estimate. -/
lemma moment_order (p θ ε : ℝ) (hp : 1 ≤ p) (ht : 1 < θ)
    (he : 0 < ε) (he2 : ε < 2) :
    let l := Nat.ceil (Real.log (2 * p / ε) / (2 * Real.log θ))
    1 ≤ l ∧ p * (1 / θ) ^ (2 * l) ≤ ε / 2 := by
  dsimp
  let l := Nat.ceil (Real.log (2 * p / ε) / (2 * Real.log θ))
  have ht0 : 0 < θ := lt_trans (by norm_num) ht
  have hlogt : 0 < Real.log θ := Real.log_pos ht
  have hx : 1 < 2 * p / ε := (lt_div_iff₀ he).2 (by nlinarith)
  have hlogx : 0 < Real.log (2 * p / ε) := Real.log_pos hx
  have hl : 1 ≤ l := Nat.ceil_pos.2 (div_pos hlogx (by positivity))
  refine ⟨hl, ?_⟩
  have hc := Nat.le_ceil (Real.log (2 * p / ε) / (2 * Real.log θ))
  have hlog : Real.log (2 * p / ε) ≤ Real.log (θ ^ (2 * l)) := by
    rw [Real.log_pow]
    have h := (div_le_iff₀ (show 0 < 2 * Real.log θ by positivity)).1 hc
    change Real.log (2 * p / ε) ≤ (2 * l : ℕ) * Real.log θ
    push_cast
    dsimp [l] at *
    nlinarith
  have hbound : 2 * p / ε ≤ θ ^ (2 * l) :=
    (Real.log_le_log_iff (by positivity) (by positivity)).1 hlog
  rw [one_div, inv_pow, ← div_eq_mul_inv]
  apply (div_le_iff₀ (pow_pos ht0 _)).2
  have h := (div_le_iff₀ he).1 hbound
  nlinarith

lemma L_pos (r : ℕ) : 1 ≤ L r := by
  exact (moment_order (P r) θ E (by exact_mod_cast P_ge_one r)
    (by norm_num) (by norm_num) (by norm_num)).1

lemma decay (r : ℕ) : (P r : ℝ) * (1 / θ) ^ (2 * L r) ≤ E / 2 := by
  exact (moment_order (P r) θ E (by exact_mod_cast P_ge_one r)
    (by norm_num) (by norm_num) (by norm_num)).2

/-- Two extra binary digits dominate the nonidentity word term. -/
lemma modulus_bound (b d l : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) :
    (b ^ (4 * l) + 1) * d ^ (2 * l) <
    2 ^ (2 + Nat.ceil ((l : ℝ) *
      (4 * (Real.log b / Real.log 2) + 2 * (Real.log d / Real.log 2)))) := by
  let z := (l : ℝ) * (4 * (Real.log b / Real.log 2) + 2 * (Real.log d / Real.log 2))
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : z ≤ (Nat.ceil z : ℝ) := Nat.le_ceil z
  have hlog : Real.log ((b : ℝ) ^ (4 * l) * (d : ℝ) ^ (2 * l)) ≤
      Real.log ((2 : ℝ) ^ Nat.ceil z) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow]
    have h := (mul_le_mul_of_nonneg_right hc hlog2.le)
    dsimp [z] at h
    push_cast
    have hz : ((l : ℝ) * (4 * (Real.log b / Real.log 2) + 2 * (Real.log d / Real.log 2))) *
        Real.log 2 = 4 * l * Real.log b + 2 * l * Real.log d := by
      field_simp
      <;> ring
    rw [hz] at h
    linarith
  have hpow : (b : ℝ) ^ (4 * l) * (d : ℝ) ^ (2 * l) ≤ (2 : ℝ) ^ Nat.ceil z :=
    (Real.log_le_log_iff (by positivity) (by positivity)).1 hlog
  have hpowN : b ^ (4 * l) * d ^ (2 * l) ≤ 2 ^ Nat.ceil z := by exact_mod_cast hpow
  have hbpow : 1 ≤ b ^ (4 * l) := one_le_pow₀ hb
  have hdpow : 0 < d ^ (2 * l) := pow_pos (by omega) _
  change _ < 2 ^ (2 + Nat.ceil z)
  rw [pow_add]
  norm_num
  nlinarith

lemma Q_large (r : ℕ) : wordBound M (L r) * k r ^ (2 * L r) < Q r := by
  exact modulus_bound (4 * M - 1) (k r) (L r) (by norm_num) (k_ge_one r)

lemma q_pos (r : ℕ) : 1 ≤ q r := by unfold q; omega

lemma Q_wordBound (r : ℕ) : wordBound M (L r) < Q r := by
  have hkp : 1 ≤ k r ^ (2 * L r) := one_le_pow₀ (k_ge_one r)
  exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) (Q_large r)

lemma traceRHS_small (r : ℕ) (hr : 1 ≤ r) :
    traceRHS C₁ (C₂ r) M r (L r) (Q r) < E := by
  have hk : (0 : ℝ) < k r := by exact_mod_cast k_pos r
  have hs : 0 < Real.sqrt C₁ := Real.sqrt_pos.2 (by norm_num)
  have hA : 1 ≤ A r := A_ge_one r hr
  have hd0 : 0 ≤ delta M r := Real.sqrt_nonneg _
  have hd2 : (delta M r) ^ 2 = A r := Real.sq_sqrt (show 0 ≤ A r by linarith)
  have hd : 1 ≤ delta M r := by nlinarith
  have hdpos : 0 < delta M r := by linarith
  have ht : 0 < θ := by norm_num
  have hc : 0 < C₂ r := by rw [C₂_eq]; positivity
  have hfirst : Real.sqrt C₁ * delta M r / C₂ r = 1 / θ := by
    rw [C₂_eq]
    field_simp [ne_of_gt hs, ne_of_gt hdpos, ne_of_gt ht] <;> ring
  have hkm1 : ((k r - 1 : ℕ) : ℝ) ≤ (k r : ℝ) := by
    exact_mod_cast Nat.sub_le (k r) 1
  have hrad : 0 ≤ C₁ * (k r : ℝ) * ((k r - 1 : ℕ) : ℝ) := by positivity
  have hsqrt : Real.sqrt (C₁ * (k r : ℝ) * ((k r - 1 : ℕ) : ℝ)) ≤
      Real.sqrt C₁ * k r := by
    calc
      _ ≤ Real.sqrt (C₁ * (k r : ℝ) ^ 2) := Real.sqrt_le_sqrt (by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ C₁ * k r by positivity)
          (sub_nonneg.mpr hkm1)])
      _ = _ := by rw [Real.sqrt_mul (show (0 : ℝ) ≤ C₁ by norm_num),
        Real.sqrt_sq (Nat.cast_nonneg (k r))]
  have hratio : Real.sqrt (C₁ * (k r : ℝ) * ((k r - 1 : ℕ) : ℝ)) / C₂ r ≤
      (k r : ℝ) / θ := by
    apply (div_le_div_iff₀ hc ht).2
    rw [C₂_eq]
    have hprod : Real.sqrt C₁ * k r ≤ (k r : ℝ) * Real.sqrt C₁ * delta M r := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ Real.sqrt C₁ * k r by positivity)
        (sub_nonneg.mpr hd)]
    nlinarith [mul_le_mul_of_nonneg_right (hsqrt.trans hprod) ht.le]
  have hpow := pow_le_pow_left₀ (div_nonneg (Real.sqrt_nonneg _) hc.le) hratio (2 * L r)
  have hQ : (0 : ℝ) < Q r := by unfold Q; positivity
  have hword : (0 : ℝ) ≤ wordBound M (L r) := Nat.cast_nonneg _
  have hsize : (wordBound M (L r) : ℝ) * (k r : ℝ) ^ (2 * L r) < Q r := by
    exact_mod_cast Q_large r
  have herror : (wordBound M (L r) : ℝ) / Q r *
      (Real.sqrt (C₁ * (k r : ℝ) * ((k r - 1 : ℕ) : ℝ)) / C₂ r) ^ (2 * L r) <
      (1 / θ) ^ (2 * L r) := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow (div_nonneg hword hQ.le))
    rw [div_pow (k r : ℝ) θ, div_pow (1 : ℝ) θ, one_pow]
    apply (lt_div_iff₀ (pow_pos ht _)).2
    have heq : (wordBound M (L r) : ℝ) / Q r *
      ((k r : ℝ) ^ (2 * L r) / θ ^ (2 * L r)) * θ ^ (2 * L r) =
        (wordBound M (L r) : ℝ) * (k r : ℝ) ^ (2 * L r) / Q r := by
      field_simp [ne_of_gt hQ, ne_of_gt ht] <;> ring
    rw [heq]
    exact (div_lt_one hQ).2 hsize
  have hp : (0 : ℝ) < P r := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (P_ge_one r))
  change (P r : ℝ) * ((Real.sqrt C₁ * delta M r / C₂ r) ^ (2 * L r) +
    (wordBound M (L r) : ℝ) / Q r *
      (Real.sqrt (C₁ * (k r : ℝ) * ((k r - 1 : ℕ) : ℝ)) / C₂ r) ^ (2 * L r)) < E
  rw [mul_add, hfirst]
  have herr := mul_lt_mul_of_pos_left herror hp
  have hdecay := decay r
  linarith

/-- The single-copy parameter in the proof agrees with the closed expression
used in the numerical entropy certificate. -/
lemma a_identity (r : ℕ) (hr : 1 ≤ r) (γ : ℝ) :
    1 + (C₂ r / (Real.sqrt C₁ - Real.sqrt 2)) ^ 2 * γ ^ 2 / (k r : ℝ) =
      1 + (10001 * γ / 9999) ^ 2 * ((1 + 9 / (M : ℝ)) ^ r - 1) := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hA : 0 ≤ A r := le_trans (by norm_num) (A_ge_one r hr)
  have hquot : C₂ r / (Real.sqrt C₁ - Real.sqrt 2) =
      (10001 / 9999 : ℝ) * Real.sqrt (A r) := by
    rw [sqrt_C₁]
    unfold C₂
    have heq : 10000 * Real.sqrt (2 : ℝ) - Real.sqrt 2 = 9999 * Real.sqrt 2 := by ring
    rw [heq]
    field_simp [hs] <;> ring
  have hkr : (k r : ℝ) = (M : ℝ) ^ r := by simp [k]
  have hratio : A r / (k r : ℝ) = (1 + 9 / (M : ℝ)) ^ r - 1 := by
    rw [A, hkr, sub_div, div_self (by positivity), ← div_pow]
    congr 2
    norm_num
  rw [hquot, mul_pow, Real.sq_sqrt hA, ← hratio]
  ring

/-- The actual filter constructed from the two quantum adders has trace error <10⁻⁶. -/
theorem prescribedFilter_small (r : ℕ) (hr : 1 ≤ r) :
    (Matrix.trace (prescribedFilter M r (L r) (q r) C₁ (C₂ r)
      (by norm_num) (by norm_num))).re / (Q r : ℝ) ^ (2 * r) < E := by
  exact (technical_trace_bound M r (L r) (q r) C₁ (C₂ r)
    (by norm_num) hr (L_pos r) (q_pos r) (by norm_num) (C₂_large r hr)
    (Q_wordBound r)).trans_lt (traceRHS_small r hr)

end MainFilterParameters
