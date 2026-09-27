import JointChannel

/-! A universal upper bound on the entropy gap relative to the proposed
reference spectrum. This applies to actual state-valued channels, independently
of the unitary tuple or suppressor. -/

noncomputable section

namespace SuppressorEntropy

/-- The entropy of the reference spectrum, parameterized directly by `s`. -/
def comparisonEntropy (k : ℕ) (s : ℝ) : ℝ :=
  Real.negMulLog ((1+s*((k:ℝ)-1))/(k:ℝ)^2) +
    ((k:ℝ)-1)*Real.negMulLog ((1-s)/(k:ℝ)^2) +
    ((k:ℝ)*((k:ℝ)-1))*Real.negMulLog (1/(k:ℝ)^2)

theorem referenceEntropy_eq_comparisonEntropy (k : ℕ) (γ ε : ℝ) :
    referenceEntropy k γ ε = comparisonEntropy k (γ^2/(1+ε)^2) := rfl

/-- The scaling identity remains valid at `x = 0`, with `0 log 0 = 0`. -/
theorem negMulLog_div_sq (k x : ℝ) :
    Real.negMulLog (x / k^2) =
      (2*x*Real.log k-x*Real.log x)/k^2 := by
  rw [div_eq_mul_inv, Real.negMulLog_mul]
  simp only [Real.negMulLog, Real.log_inv, Real.log_pow]
  ring

/-- Exact entropy deficit. The `k(k-1)` unchanged eigenvalues cancel. -/
theorem comparisonEntropy_deficit (k : ℕ) (hk : 0 < k) (s : ℝ) :
    2*Real.log k - comparisonEntropy k s =
      ((1+((k:ℝ)-1)*s)*Real.log (1+((k:ℝ)-1)*s) +
        ((k:ℝ)-1)*(1-s)*Real.log (1-s))/(k:ℝ)^2 := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [comparisonEntropy, negMulLog_div_sq, Real.log_one, mul_zero]
  have heq : 1+s*((k:ℝ)-1) = 1+((k:ℝ)-1)*s := by ring
  rw [heq]
  field_simp
  ring

/-- Convexity of `x log x` bounds its value between 1 and `k`. -/
theorem mul_log_interpolation (k s : ℝ) (hk : 0 ≤ k)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1+(k-1)*s)*Real.log (1+(k-1)*s) ≤ s*k*Real.log k := by
  have h := Real.convexOn_mul_log.2 (show 1 ∈ Set.Ici (0:ℝ) by simp)
    hk (show 0 ≤ 1-s by linarith) hs0 (show 1-s+s=1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at h
  rw [show 1+(k-1)*s = (1-s)*1+s*k by ring]
  simpa only [mul_assoc] using h

/-- The reference entropy loses at most `s log k / k` from `2 log k`. -/
theorem comparisonEntropy_deficit_le (k : ℕ) (hk : 1 ≤ k) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    2*Real.log k - comparisonEntropy k s ≤ s*(Real.log k/(k:ℝ)) := by
  have hk1 : 1 ≤ (k:ℝ) := by exact_mod_cast hk
  have hk0 : (k:ℝ) ≠ 0 := by linarith
  have hkpos : 0 < k := by omega
  rw [comparisonEntropy_deficit k hkpos s]
  have ha := mul_log_interpolation (k:ℝ) s (by positivity) hs0 hs1
  have hb : ((k:ℝ)-1)*(1-s)*Real.log (1-s) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by linarith) (by linarith))
      (Real.log_nonpos (by linarith) (by linarith))
  calc
    _ ≤ (s*(k:ℝ)*Real.log k)/(k:ℝ)^2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = s*(Real.log k/(k:ℝ)) := by field_simp

/-- Every state-valued channel has minimum output entropy at most `log k`. -/
theorem minimumOutputEntropy_le_log_dimension {n k : ℕ}
    (Φ : MState (Fin n) → MState (Fin k)) (hn : 0 < n) :
    minimumOutputEntropy Φ ≤ Real.log k := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := (minimumOutputEntropy_le Φ MState.uniform).trans
    (Sᵥₙ_le_log_d (Φ MState.uniform))
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- Universal obstruction for actual channels and the proposed reference spectrum. -/
theorem gap_le_comparison_deficit {n k : ℕ}
    (Φ : MState (Fin n) → MState (Fin k)) (hn : 0 < n)
    (hk : 1 ≤ k) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    2*minimumOutputEntropy Φ - comparisonEntropy k s ≤
      s*(Real.log k/(k:ℝ)) := by
  have hmin := minimumOutputEntropy_le_log_dimension Φ hn
  have href := comparisonEntropy_deficit_le k hk s hs0 hs1
  linarith

/-- Strong parameter-dependent upper bound, independently of all unitaries and `Q`. -/
theorem universal_reference_gap_scaled {n k : ℕ}
    (Φ : MState (Fin n) → MState (Fin k)) (hn : 0 < n)
    (hk : 2 ≤ k) (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) :
    2*minimumOutputEntropy Φ - referenceEntropy k γ ε ≤
      (γ^2/(1+ε)^2)*(Real.log k/(k:ℝ)) := by
  rw [referenceEntropy_eq_comparisonEntropy]
  apply gap_le_comparison_deficit Φ hn (by omega)
  · positivity
  · apply (div_le_one (by positivity : 0 < (1+ε)^2)).mpr
    nlinarith

/-- The proposed gap can never exceed `log k / k`. -/
theorem universal_reference_gap {n k : ℕ}
    (Φ : MState (Fin n) → MState (Fin k)) (hn : 0 < n)
    (hk : 2 ≤ k) (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) :
    2*minimumOutputEntropy Φ - referenceEntropy k γ ε ≤
      Real.log k/(k:ℝ) := by
  have hs1 : γ^2/(1+ε)^2 ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (1+ε)^2)).mpr
    nlinarith
  have hlog : 0 ≤ Real.log k/(k:ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ (γ^2/(1+ε)^2)*(Real.log k/(k:ℝ)) :=
      universal_reference_gap_scaled Φ hn hk γ ε hγ0 hγ1 hε
    _ ≤ 1*(Real.log k/(k:ℝ)) := mul_le_mul_of_nonneg_right hs1 hlog
    _ = _ := one_mul _

#print axioms comparisonEntropy_deficit
#print axioms universal_reference_gap_scaled
#print axioms universal_reference_gap

end SuppressorEntropy
