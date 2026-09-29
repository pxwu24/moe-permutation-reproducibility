import TensorAmplification

/-!
# Symbolic amplification estimates

The numerical entropy slope is proved from its exact reference spectrum.
The amplification statements are conditional on the single-copy and
coordinate-pair entropy hypotheses, as explicitly stated in their types.
They do not postulate these inequalities as axioms, nor formalize the
finite-group or filter construction supplying them.
-/

noncomputable section

namespace SuppressorEntropy

/-- The lower estimate for the reference entropy deficit. -/
theorem comparison_deficit_lower (M : ℕ) (hM : 1 ≤ M)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (s * Real.log M - EntropyGapRemainder.binaryEntropy s) / M ≤
      2 * Real.log M - comparisonEntropy M s := by
  have h := (comparisonEntropy_sharp_remainder M hM s hs0 hs1).1
  linarith

/-- A quantitative lower bound for the slope in the user's amplification corollary. -/
theorem symbolic_slope_lower (M : ℕ) (hM : 1 ≤ M)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (s * Real.log M - EntropyGapRemainder.binaryEntropy s - 18) / M ≤
      amplificationSlope M s 9 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hD := comparison_deficit_lower M hM s hs0 hs1
  have hlog : Real.log (1 + 9 / (M : ℝ)) ≤ 9 / (M : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 9 / (M : ℝ) by positivity)
    linarith
  unfold amplificationSlope
  have hid : (s * Real.log M - EntropyGapRemainder.binaryEntropy s - 18) / M =
      (s * Real.log M - EntropyGapRemainder.binaryEntropy s) / M -
        2 * (9 / (M : ℝ)) := by ring
  rw [hid]
  linarith

/-- The dimension criterion has no fixed numerical choices of `M` or `s`. -/
theorem symbolic_slope_positive (M : ℕ) (hM : 1 ≤ M)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hcriterion : 18 < s * Real.log M - EntropyGapRemainder.binaryEntropy s) :
    0 < amplificationSlope M s 9 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  exact (div_pos (by linarith) hM0).trans_le
    (symbolic_slope_lower M hM s hs0 hs1)

/-- Every fixed positive `s` satisfies the criterion in every sufficiently large
natural output-base dimension. This is an explicit Archimedean argument. -/
theorem eventually_dimension_criterion (s : ℝ) (hs0 : 0 < s) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      18 < s * Real.log M - EntropyGapRemainder.binaryEntropy s := by
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt
    (max (2 : ℝ) (Real.exp ((18 + EntropyGapRemainder.binaryEntropy s) / s)))
  have hM₀two : (2 : ℝ) < M₀ := (le_max_left _ _).trans_lt hM₀
  have hM₀nat : 2 ≤ M₀ := by exact_mod_cast hM₀two.le
  refine ⟨M₀, hM₀nat, ?_⟩
  intro M hM
  have hMM₀ : (M₀ : ℝ) ≤ M := by exact_mod_cast hM
  have hexp : Real.exp ((18 + EntropyGapRemainder.binaryEntropy s) / s) < M :=
    ((le_max_right _ _).trans_lt hM₀).trans_le hMM₀
  have hlog := Real.strictMonoOn_log (Real.exp_pos _)
    ((Real.exp_pos _).trans hexp) hexp
  rw [Real.log_exp] at hlog
  have hmul := (div_lt_iff₀ hs0).mp hlog
  nlinarith

/-- The physical parameters produce `s` strictly between zero and one. -/
theorem filter_signal_mem_Ioo (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) : 0 < γ ^ 2 / (1 + ε) ^ 2 ∧ γ ^ 2 / (1 + ε) ^ 2 < 1 := by
  constructor
  · positivity
  · apply (div_lt_one (by positivity : 0 < (1 + ε) ^ 2)).mpr
    nlinarith

/-- For every fixed admissible signal and trace budget, all sufficiently large
base dimensions have a strictly positive entropy slope. -/
theorem physical_parameters_eventually_positive_slope (γ ε : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      0 < amplificationSlope M (γ ^ 2 / (1 + ε) ^ 2) 9 := by
  have hs := filter_signal_mem_Ioo γ ε hγ0 hγ1 hε
  obtain ⟨M₀, hM₀, hcriterion⟩ := eventually_dimension_criterion _ hs.1
  refine ⟨M₀, hM₀, ?_⟩
  intro M hM
  exact symbolic_slope_positive M (by omega) _ hs.1 hs.2 (hcriterion M hM)

/-- Logarithmic simplification retaining the complete `c` dependence. -/
theorem support_entropy_cost_bound (γ c B : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hc : 1 ≤ c) (hB : 1 ≤ B) :
    Real.log (1 + γ ^ 2 * c ^ 2 * (B - 1)) ≤
      Real.log B + 2 * Real.log c := by
  have hc0 : 0 < c := by linarith
  have hB0 : 0 < B := by linarith
  have hg2 : γ ^ 2 ≤ 1 := by nlinarith
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hg2
    (show 0 ≤ c ^ 2 * (B - 1) by positivity)
  have harg : 0 < 1 + γ ^ 2 * c ^ 2 * (B - 1) := by positivity
  have hargle : 1 + γ ^ 2 * c ^ 2 * (B - 1) ≤ c ^ 2 * B := by
    nlinarith
  have hlog := Real.log_le_log harg hargle
  rw [Real.log_mul (by positivity : c ^ 2 ≠ 0) hB0.ne', Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

/-- Exact scalar combination of the two entropy estimates, including `-4 log c`. -/
theorem symbolic_tensor_gap (M r : ℕ) (hM : 1 ≤ M)
    (γ c s single joint : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hc : 1 ≤ c)
    (hsingle : (r : ℝ) * Real.log M -
      Real.log (1 + γ ^ 2 * c ^ 2 * ((1 + 9 / (M : ℝ)) ^ r - 1)) ≤ single)
    (hjoint : joint ≤ (r : ℝ) * comparisonEntropy M s) :
    (r : ℝ) * amplificationSlope M s 9 - 4 * Real.log c ≤
      2 * single - joint := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hbase : (1 : ℝ) ≤ 1 + 9 / (M : ℝ) := by
    have hpos : (0 : ℝ) ≤ 9 / (M : ℝ) := by positivity
    linarith
  have hB : (1 : ℝ) ≤ (1 + 9 / (M : ℝ)) ^ r := one_le_pow₀ hbase
  have hcost := support_entropy_cost_bound γ c ((1 + 9 / (M : ℝ)) ^ r)
    hγ0 hγ1 hc hB
  rw [Real.log_pow] at hcost
  unfold amplificationSlope
  nlinarith

/-- A family of gaps satisfying the symbolic lower bound exceeds every real target. -/
theorem unbounded_from_symbolic_gap (α c : ℝ) (hα : 0 < α)
    (single joint : ℕ → ℝ)
    (hgap : ∀ r : ℕ, 0 < r → (r : ℝ) * α - 4 * Real.log c ≤
      2 * single r - joint r) (target : ℝ) :
    ∃ r : ℕ, 0 < r ∧ target < 2 * single r - joint r := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max 0 ((target + 4 * Real.log c) / α))
  have hr0 : (0 : ℝ) < r := (le_max_left _ _).trans_lt hr
  have hrNat : 0 < r := by exact_mod_cast hr0
  have hrt : (target + 4 * Real.log c) / α < (r : ℝ) :=
    (le_max_right _ _).trans_lt hr
  have htarget := (div_lt_iff₀ hα).mp hrt
  refine ⟨r, hrNat, ?_⟩
  have hg := hgap r hrNat
  nlinarith

/-- The same lower bound proves divergence, and not merely unboundedness. -/
theorem symbolic_gap_tendsto_atTop (α c : ℝ) (hα : 0 < α)
    (single joint : ℕ → ℝ)
    (hgap : ∀ r : ℕ, 0 < r → (r : ℝ) * α - 4 * Real.log c ≤
      2 * single r - joint r) :
    Filter.Tendsto (fun r : ℕ => 2 * single r - joint r)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro target
  obtain ⟨R, hR⟩ := exists_nat_gt (max 0 ((target + 4 * Real.log c) / α))
  filter_upwards [Filter.eventually_ge_atTop R] with r hr
  have hRr : (R : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := ((le_max_left _ _).trans_lt hR).trans_le hRr
  have hrNat : 0 < r := by exact_mod_cast hr0
  have hrt : (target + 4 * Real.log c) / α < (r : ℝ) :=
    ((le_max_right _ _).trans_lt hR).trans_le hRr
  have htarget := (div_lt_iff₀ hα).mp hrt
  have hg := hgap r hrNat
  nlinarith

/-- The scalar corollary for actual minimum output entropies. The single and joint
entropy hypotheses are explicit: this theorem does not prove the channel construction. -/
theorem channel_symbolic_tensor_gap {n k nj kj : ℕ}
    (Φ : MState (Fin n) → MState (Fin k))
    (Joint : MState (Fin nj) → MState (Fin kj))
    (M r : ℕ) (hM : 1 ≤ M) (γ ε c : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hc : 1 ≤ c)
    (hsingle : (r : ℝ) * Real.log M -
      Real.log (1 + γ ^ 2 * c ^ 2 * ((1 + 9 / (M : ℝ)) ^ r - 1)) ≤
        minimumOutputEntropy Φ)
    (hjoint : minimumOutputEntropy Joint ≤
      (r : ℝ) * referenceEntropy M γ ε) :
    (r : ℝ) * amplificationSlope M (γ ^ 2 / (1 + ε) ^ 2) 9 - 4 * Real.log c ≤
      2 * minimumOutputEntropy Φ - minimumOutputEntropy Joint := by
  apply symbolic_tensor_gap M r hM γ c (γ ^ 2 / (1 + ε) ^ 2)
    (minimumOutputEntropy Φ) (minimumOutputEntropy Joint) hγ0 hγ1 hc hsingle
  simpa only [referenceEntropy_eq_comparisonEntropy] using hjoint

/-- Complete scalar amplification criterion for arbitrary physical parameters. -/
theorem symbolic_unbounded_violation (M : ℕ) (hM : 1 ≤ M) (γ ε c : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) (hc : 1 ≤ c)
    (hcriterion : 18 < (γ ^ 2 / (1 + ε) ^ 2) * Real.log M -
      EntropyGapRemainder.binaryEntropy (γ ^ 2 / (1 + ε) ^ 2))
    (single joint : ℕ → ℝ)
    (hsingle : ∀ r : ℕ, 0 < r → (r : ℝ) * Real.log M -
      Real.log (1 + γ ^ 2 * c ^ 2 * ((1 + 9 / (M : ℝ)) ^ r - 1)) ≤ single r)
    (hjoint : ∀ r : ℕ, 0 < r → joint r ≤
      (r : ℝ) * referenceEntropy M γ ε)
    (target : ℝ) : ∃ r : ℕ, 0 < r ∧ target < 2 * single r - joint r := by
  have hs := filter_signal_mem_Ioo γ ε hγ0 hγ1 hε
  have hα := symbolic_slope_positive M hM (γ ^ 2 / (1 + ε) ^ 2)
    hs.1 hs.2 hcriterion
  apply unbounded_from_symbolic_gap _ c hα single joint _ target
  intro r hr
  apply symbolic_tensor_gap M r hM γ c (γ ^ 2 / (1 + ε) ^ 2)
    (single r) (joint r) hγ0.le hγ1.le hc (hsingle r hr)
  simpa only [referenceEntropy_eq_comparisonEntropy] using hjoint r hr

#print axioms comparison_deficit_lower
#print axioms symbolic_slope_lower
#print axioms symbolic_slope_positive
#print axioms eventually_dimension_criterion
#print axioms filter_signal_mem_Ioo
#print axioms physical_parameters_eventually_positive_slope
#print axioms support_entropy_cost_bound
#print axioms symbolic_tensor_gap
#print axioms unbounded_from_symbolic_gap
#print axioms symbolic_gap_tendsto_atTop
#print axioms channel_symbolic_tensor_gap
#print axioms symbolic_unbounded_violation

end SuppressorEntropy
