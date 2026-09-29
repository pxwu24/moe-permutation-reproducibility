import MainTheorem

/-!
# The sharper postprocessing bounds in the revised Supplement

The affine one-copy bound satisfies `a r ≤ beta * (1 + 9 / M)^r`.
Keeping `beta` outside the power gives the revised asymptotic slope
`d_M(s) - 2 log(1 + 9/M)`.  The error term is explicit below, and the
two-copy entropy estimate concerns the actual Bell output, as required
by the subsequent Holevo lower bound.
-/

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
open MainParameters MainHolevo

namespace MainSharperPostprocessing

/-- The fixed prefactor does not contribute to the asymptotic slope. -/
theorem a_le_beta_power (r : ℕ) :
    a r ≤ beta * (1 + 9 / (M : ℝ)) ^ r := by
  have hb := beta_bounds.1
  unfold a
  nlinarith

theorem log_a_le_sharp (r : ℕ) :
    Real.log (a r) ≤ Real.log beta +
      (r : ℝ) * Real.log (1 + 9 / (M : ℝ)) := by
  have h := Real.log_le_log (a_pos r) (a_le_beta_power r)
  rw [Real.log_mul (by linarith [beta_bounds.1]) (by positivity),
    Real.log_pow] at h
  exact h

/-- In particular, the revised slope is strictly positive. -/
theorem numerical_margin_sharp :
    (5 : ℝ) / 1000000000 <
      EntropyGapRemainder.entropyDeficit (M : ℝ) s0 -
        2 * Real.log (1 + 9 / (M : ℝ)) := by
  have hbase : 1 + 9 / (M : ℝ) ≤ 1 + 9 * beta / (M : ℝ) := by
    norm_num [M]
    linarith [beta_bounds.1]
  have hlog := Real.log_le_log (by norm_num [M] : 0 < 1 + 9 / (M : ℝ)) hbase
  linarith [numerical_margin]

/-- The logarithmic seed count with the revised linear coefficient. -/
theorem log_randomizerSize_bound_sharp (r : ℕ) (hr : 1 ≤ r) :
    Real.log (randomizerSize r : ℝ) <
      2 * Real.log 108 + 4 * Real.log (r : ℝ) + Real.log beta +
        (r : ℝ) * Real.log (1 + 9 / (M : ℝ)) := by
  have hsize := log_randomizerSize_bound r hr
  have ha := log_a_le_sharp r
  linarith

/-- The revised two-copy bound, for the actual Bell input and with the
`O(log r)` term replaced by a certified explicit expression. -/
theorem two_copy_sharp (r : ℕ) (hr : 1 ≤ r) :
    Sᵥₙ (((MainConcreteSmoothed.channel r hr).prod
      (MainConcreteSmoothed.channel r hr))
      (MState.pure (Ket.MES (Fin (MainConcreteBasic.inputDimension r))))) ≤
      2 * Real.log (M ^ r) - (r : ℝ) *
        (EntropyGapRemainder.entropyDeficit (M : ℝ) s0 -
          2 * Real.log (1 + 9 / (M : ℝ))) +
        8 * Real.log (r : ℝ) + 4 * Real.log 108 + 2 * Real.log beta := by
  have he := MainConcreteSmoothed.two_copy r hr
  have hcost := log_randomizerSize_bound_sharp r hr
  linarith

/-- The matching two-copy Holevo bound for the final, explicitly defined
channel. It uses the Bell-output estimate, not merely minimum output entropy. -/
theorem holevo_two_copy_sharp (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) * (EntropyGapRemainder.entropyDeficit (M : ℝ) s0 -
      2 * Real.log (1 + 9 / (M : ℝ))) -
      8 * Real.log (r : ℝ) - 4 * Real.log 108 - 2 * Real.log beta ≤
        holevo ((MainTheorem.channel r hr).prod (MainTheorem.channel r hr)) := by
  have he := two_copy_sharp r hr
  have hw := MainPauliHolevo.completion_tensor_holevo_lower
    (MainConcreteSmoothed.channel r hr)
    (MState.pure (Ket.MES (Fin (MainConcreteBasic.inputDimension r))))
  rw [show Fintype.card (MainPauli.Bits (27 * r)) = MainFilterParameters.k r
    from MainTheorem.output_card r] at hw
  change _ ≤ holevo ((MainTheorem.channel r hr).prod (MainTheorem.channel r hr)) at hw
  have hM : M = MainFilterParameters.M := by norm_num [M]
  simp only [hM, MainFilterParameters.k, Nat.cast_pow] at he hw ⊢
  convert (sub_le_sub_left he
    (2 * Real.log ((MainFilterParameters.M : ℝ) ^ r))).trans hw using 1 <;>
    first | rfl | ring

end MainSharperPostprocessing

#print axioms MainSharperPostprocessing.numerical_margin_sharp
#print axioms MainSharperPostprocessing.two_copy_sharp
#print axioms MainSharperPostprocessing.holevo_two_copy_sharp
