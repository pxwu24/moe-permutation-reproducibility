import GapAsymptotics
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A scalar amplification criterion for the tensor-marginal comparison

This file does not assert the new quantum-channel entropy hypotheses.
It checks their scalar consequences and a concrete positive slope.
The final three theorems include the filter loss `2 * log (16 / 9)` in
the single-copy hypothesis; they are the variants applicable to the estimates
established in the accompanying mathematical argument.
-/

noncomputable section

namespace SuppressorEntropy

/-- Here `cost = 9` is the single-copy entropy cost. It is distinct from the
filter constant `c = 16/9` appearing in the final three theorems. -/
def amplificationSlope (M : ℕ) (s cost : ℝ) : ℝ :=
  2 * Real.log M - comparisonEntropy M s - 2 * Real.log (1 + cost / M)

/-- If the single-copy estimate and the stronger tensor-marginal joint estimate
hold, the gap is at least `r` times this fixed slope. -/
theorem tensor_marginal_scalar_amplification (M : ℕ) (s cost r single joint : ℝ)
    (_hr : 0 ≤ r)
    (hsingle : r * Real.log M - r * Real.log (1 + cost / M) ≤ single)
    (hjoint : joint ≤ r * comparisonEntropy M s) :
    r * amplificationSlope M s cost ≤ 2 * single - joint := by
  unfold amplificationSlope
  nlinarith

theorem binaryEntropy_le_log_two (s : ℝ) :
    EntropyGapRemainder.binaryEntropy s ≤ Real.log 2 := by
  have h := Real.binEntropy_le_log_two (p := s)
  simpa only [EntropyGapRemainder.binaryEntropy, Real.binEntropy,
    Real.log_inv, mul_neg, neg_mul, sub_eq_add_neg] using h

abbrev amplificationBase : ℕ := 2 ^ 32

def amplificationS : ℝ := ((255 : ℝ) / 257) ^ 2

/-- An explicit positive slope; the only transcendental numerical ingredient
is mathlib's rigorously proved lower bound on `log 2`. -/
theorem concrete_amplification_slope :
    3 / (amplificationBase : ℝ) <
      amplificationSlope amplificationBase amplificationS 9 := by
  have hM : 1 ≤ amplificationBase := by norm_num [amplificationBase]
  have hM0 : (0 : ℝ) < amplificationBase := by norm_num [amplificationBase]
  have hs0 : 0 < amplificationS := by norm_num [amplificationS]
  have hs1 : amplificationS < 1 := by norm_num [amplificationS]
  have hs : (63 : ℝ) / 64 < amplificationS := by norm_num [amplificationS]
  have hlog2 : (56 : ℝ) / 81 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogM : Real.log (amplificationBase : ℝ) = 32 * Real.log 2 := by
    simp only [amplificationBase, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hnum : 21 < amplificationS * Real.log amplificationBase - Real.log 2 := by
    rw [hlogM]
    nlinarith
  have hrem := (comparisonEntropy_sharp_remainder amplificationBase hM
    amplificationS hs0 hs1).1
  have hbin := binaryEntropy_le_log_two amplificationS
  have hD :
      (amplificationS * Real.log amplificationBase - Real.log 2) / amplificationBase ≤
        2 * Real.log amplificationBase - comparisonEntropy amplificationBase amplificationS := by
    have hdiv := div_le_div_of_nonneg_right
      (sub_le_sub_left hbin (amplificationS * Real.log amplificationBase)) hM0.le
    linarith
  have hlog : Real.log (1 + 9 / (amplificationBase : ℝ)) ≤
      9 / (amplificationBase : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 9 / (amplificationBase : ℝ) by positivity)
    linarith
  unfold amplificationSlope
  have hnumdiv : 3 / (amplificationBase : ℝ) <
      (amplificationS * Real.log amplificationBase - Real.log 2 - 18) / amplificationBase :=
    (div_lt_div_iff_of_pos_right hM0).mpr (by linarith)
  have hid :
      (amplificationS * Real.log amplificationBase - Real.log 2 - 18) / amplificationBase =
      (amplificationS * Real.log amplificationBase - Real.log 2) / amplificationBase -
        2 * (9 / (amplificationBase : ℝ)) := by ring
  rw [hid] at hnumdiv
  linarith

/-- A conditional linear lower bound with completely explicit parameters. -/
theorem concrete_tensor_marginal_gap (r single joint : ℝ) (hr : 0 < r)
    (hsingle : r * Real.log amplificationBase -
      r * Real.log (1 + 9 / (amplificationBase : ℝ)) ≤ single)
    (hjoint : joint ≤ r * comparisonEntropy amplificationBase amplificationS) :
    3 * r / amplificationBase < 2 * single - joint := by
  have h := tensor_marginal_scalar_amplification amplificationBase amplificationS 9
    r single joint hr.le hsingle hjoint
  have hc := mul_lt_mul_of_pos_left concrete_amplification_slope hr
  calc
    3 * r / amplificationBase = r * (3 / (amplificationBase : ℝ)) := by ring
    _ < r * amplificationSlope amplificationBase amplificationS 9 := hc
    _ ≤ 2 * single - joint := h

/-- The preceding hypotheses imply gaps above every prescribed threshold.
The hypotheses must be proved separately for the proposed channels. -/
theorem conditional_unbounded_tensor_marginal_gap (single joint : ℕ → ℝ)
    (hsingle : ∀ r : ℕ, (r : ℝ) * Real.log amplificationBase -
      (r : ℝ) * Real.log (1 + 9 / (amplificationBase : ℝ)) ≤ single r)
    (hjoint : ∀ r : ℕ, joint r ≤
      (r : ℝ) * comparisonEntropy amplificationBase amplificationS)
    (target : ℝ) :
    ∃ r : ℕ, target < 2 * single r - joint r := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max 0 (target * amplificationBase / 3))
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr
  have ht : target * amplificationBase / 3 < (r : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hr
  have hM0 : (0 : ℝ) < amplificationBase := by norm_num [amplificationBase]
  have ht' : target < 3 * (r : ℝ) / amplificationBase := by
    apply (lt_div_iff₀ hM0).mpr
    simpa only [mul_comm] using (div_lt_iff₀ (show (0 : ℝ) < 3 by norm_num)).mp ht
  exact ⟨r, ht'.trans (concrete_tensor_marginal_gap r (single r) (joint r)
    hr0 (hsingle r) (hjoint r))⟩

/-- The actual scalar hypothesis includes the filter constant `c = 16/9`.
It produces the corresponding constant entropy loss without changing the slope. -/
theorem concrete_tensor_marginal_gap_with_filter_constant (r single joint : ℝ)
    (hr : 0 < r)
    (hsingle : r * Real.log amplificationBase -
      r * Real.log (1 + 9 / (amplificationBase : ℝ)) -
      2 * Real.log ((16 : ℝ) / 9) ≤ single)
    (hjoint : joint ≤ r * comparisonEntropy amplificationBase amplificationS) :
    3 * r / amplificationBase - 4 * Real.log ((16 : ℝ) / 9) <
      2 * single - joint := by
  have hsingle' : r * Real.log amplificationBase -
      r * Real.log (1 + 9 / (amplificationBase : ℝ)) ≤
      single + 2 * Real.log ((16 : ℝ) / 9) := by linarith
  have h := concrete_tensor_marginal_gap r
    (single + 2 * Real.log ((16 : ℝ) / 9)) joint hr hsingle' hjoint
  linarith

/-- A simpler rigorous constant loss: `4 log (16/9) < 4`. -/
theorem concrete_tensor_marginal_gap_with_bounded_intercept (r single joint : ℝ)
    (hr : 0 < r)
    (hsingle : r * Real.log amplificationBase -
      r * Real.log (1 + 9 / (amplificationBase : ℝ)) -
      2 * Real.log ((16 : ℝ) / 9) ≤ single)
    (hjoint : joint ≤ r * comparisonEntropy amplificationBase amplificationS) :
    3 * r / amplificationBase - 4 < 2 * single - joint := by
  have h := concrete_tensor_marginal_gap_with_filter_constant r single joint
    hr hsingle hjoint
  have hc : Real.log ((16 : ℝ) / 9) < 1 := by
    have hc' := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 16 / 9 by norm_num)
    linarith
  linarith

/-- With the filter loss included, the conditional gap still exceeds every
prescribed real threshold for some positive natural tensor exponent. -/
theorem conditional_unbounded_tensor_marginal_gap_with_filter_constant
    (single joint : ℕ → ℝ)
    (hsingle : ∀ r : ℕ, 0 < r → (r : ℝ) * Real.log amplificationBase -
      (r : ℝ) * Real.log (1 + 9 / (amplificationBase : ℝ)) -
      2 * Real.log ((16 : ℝ) / 9) ≤ single r)
    (hjoint : ∀ r : ℕ, 0 < r → joint r ≤
      (r : ℝ) * comparisonEntropy amplificationBase amplificationS)
    (target : ℝ) :
    ∃ r : ℕ, 0 < r ∧ target < 2 * single r - joint r := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max 0 ((target + 4) * amplificationBase / 3))
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hrNat : 0 < r := by exact_mod_cast hr0
  have ht : (target + 4) * amplificationBase / 3 < (r : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hr
  have hM0 : (0 : ℝ) < amplificationBase := by norm_num [amplificationBase]
  have ht' : target + 4 < 3 * (r : ℝ) / amplificationBase := by
    apply (lt_div_iff₀ hM0).mpr
    simpa only [mul_comm] using (div_lt_iff₀ (show (0 : ℝ) < 3 by norm_num)).mp ht
  have hgap := concrete_tensor_marginal_gap_with_bounded_intercept r
    (single r) (joint r) hr0 (hsingle r hrNat) (hjoint r hrNat)
  refine ⟨r, ?_, ?_⟩
  · exact hrNat
  · linarith

#print axioms tensor_marginal_scalar_amplification
#print axioms concrete_amplification_slope
#print axioms concrete_tensor_marginal_gap
#print axioms conditional_unbounded_tensor_marginal_gap
#print axioms concrete_tensor_marginal_gap_with_filter_constant
#print axioms concrete_tensor_marginal_gap_with_bounded_intercept
#print axioms conditional_unbounded_tensor_marginal_gap_with_filter_constant

end SuppressorEntropy
