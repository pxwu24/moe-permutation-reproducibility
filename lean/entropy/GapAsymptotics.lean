import GapObstruction
import GapRemainder
import Mathlib.Analysis.SpecificLimits.Normed

/-! # A. The reference-state gap cannot grow with the tensor parameter -/

noncomputable section
open Filter Topology

namespace SuppressorEntropy

/-- The exact missing exponential factor when the output dimension is `M^r`. -/
lemma tensor_envelope_identity (M r : ℕ) :
    Real.log (M^r : ℕ) / (M^r : ℕ) =
      (r:ℝ)*Real.log M/(M:ℝ)^r := by
  simp only [Nat.cast_pow, Real.log_pow]

/-- Polynomial growth divided by a fixed exponential tends to zero. -/
lemma tensor_envelope_tendsto_zero (M : ℕ) (hM : 2 ≤ M) :
    Tendsto (fun r : ℕ => Real.log (M^r : ℕ) / (M^r : ℕ)) atTop (𝓝 0) := by
  have hM' : (1:ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have h := (tendsto_pow_const_div_const_pow_of_one_lt 1 hM').mul_const (Real.log M)
  simpa only [Nat.cast_pow, Real.log_pow, pow_one, div_mul_eq_mul_div,
    zero_mul] using h

/-- A dimension-independent upper bound: `log x / x ≤ 1/e`. -/
lemma log_div_le_inverse_e (x : ℝ) (hx : 0 < x) :
    Real.log x / x ≤ 1 / Real.exp 1 := by
  have he := Real.exp_pos (1:ℝ)
  have h := Real.log_le_sub_one_of_pos (div_pos hx he)
  rw [Real.log_div hx.ne' he.ne', Real.log_exp] at h
  have hlog : Real.log x ≤ x / Real.exp 1 := by linarith
  apply (div_le_div_iff₀ hx he).mpr
  simpa only [one_mul] using (le_div_iff₀ he).mp hlog

/-- Explicit `r M^{-r}` bound for the actual channel's proposed certificate. -/
lemma tensor_parameter_gap_upper {n M r : ℕ}
    (Φ : MState (Fin n) → MState (Fin (M^r))) (hn : 0 < n)
    (hM : 2 ≤ M) (hr : 0 < r)
    (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) :
    2*minimumOutputEntropy Φ - referenceEntropy (M^r) γ ε ≤
      (γ^2/(1+ε)^2)*((r:ℝ)*Real.log M/(M:ℝ)^r) := by
  have hk : 2 ≤ M^r :=
    hM.trans (le_self_pow₀ (show 1 ≤ M by omega) hr.ne')
  have h := universal_reference_gap_scaled Φ hn hk γ ε hγ0 hγ1 hε
  rwa [tensor_envelope_identity] at h

/-- Uniform boundedness independently of every filter and group parameter. -/
lemma reference_gap_le_inverse_e {n k : ℕ}
    (Φ : MState (Fin n) → MState (Fin k)) (hn : 0 < n) (hk : 2 ≤ k)
    (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) :
    2*minimumOutputEntropy Φ - referenceEntropy k γ ε ≤ 1 / Real.exp 1 := by
  exact (universal_reference_gap Φ hn hk γ ε hγ0 hγ1 hε).trans
    (log_div_le_inverse_e k (by exact_mod_cast (show 0 < k by omega)))

/-- Even when channels, input dimensions, and filter parameters vary with `r`,
the proposed certificate is eventually below every positive constant. -/
lemma tensor_parameter_gap_eventually_lt
    (M : ℕ) (hM : 2 ≤ M)
    (n : ℕ → ℕ) (hn : ∀ r, 0 < n r)
    (Φ : (r : ℕ) → MState (Fin (n r)) → MState (Fin (M^r)))
    (γ ε : ℕ → ℝ) (hγ0 : ∀ r, 0 < γ r) (hγ1 : ∀ r, γ r < 1)
    (hε : ∀ r, 0 < ε r) (d : ℝ) (hd : 0 < d) :
    ∀ᶠ r in atTop,
      2*minimumOutputEntropy (Φ r) - referenceEntropy (M^r) (γ r) (ε r) < d := by
  have he := (tendsto_order.mp (tensor_envelope_tendsto_zero M hM)).2 d hd
  filter_upwards [he, eventually_ge_atTop 1] with r her hr
  have hk : 2 ≤ M^r :=
    hM.trans (le_self_pow₀ (show 1 ≤ M by omega) (by omega))
  exact (universal_reference_gap (Φ r) (hn r) hk (γ r) (ε r)
    (hγ0 r) (hγ1 r) (hε r)).trans_lt her

#print axioms tensor_envelope_tendsto_zero
#print axioms tensor_parameter_gap_upper
#print axioms reference_gap_le_inverse_e
#print axioms tensor_parameter_gap_eventually_lt

/-- The sharp error term applies to precisely the reference spectrum. -/
lemma comparisonEntropy_sharp_remainder (k : ℕ) (hk : 1 ≤ k)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    0 ≤ (2*Real.log k-comparisonEntropy k s) -
        (s*Real.log k-EntropyGapRemainder.binaryEntropy s)/k ∧
    (2*Real.log k-comparisonEntropy k s) -
        (s*Real.log k-EntropyGapRemainder.binaryEntropy s)/k ≤
      (1-s)/(k:ℝ)^2*(Real.log k+1-Real.log (1-s)) := by
  have heq : EntropyGapRemainder.entropyDeficit (k:ℝ) s =
      2*Real.log k-comparisonEntropy k s :=
    (comparisonEntropy_deficit k (by omega) s).symm
  have h := EntropyGapRemainder.entropyDeficit_remainder_bounds (k:ℝ) s
    (by exact_mod_cast hk) hs0 hs1
  rwa [heq] at h

#print axioms comparisonEntropy_sharp_remainder

end SuppressorEntropy
