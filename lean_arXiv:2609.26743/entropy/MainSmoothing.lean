import SingleEntropy

/-!
# Main theorem: the one-copy smoothing estimate

The randomizer is an actual unital real-linear map on Hermitian matrices.
Its trace-zero Hilbert--Schmidt contraction, combined with the pointwise
bound on the basic channel, proves the smoothed minimum-output entropy
bound. No entropy conclusion is assumed.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace
open SuppressorEntropy

namespace MainSmoothing

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Hermitian-matrix norm is the unnormalized Hilbert--Schmidt norm. -/
theorem norm_sq_eq_entry_sum (Y : HermitianMat d ℂ) :
    ‖Y‖ ^ 2 = ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  rw [HermitianMat.norm_eq_frobenius, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (by positivity)

/-- The scalar cancellation that makes the smoothed estimate independent of a. -/
theorem smoothing_scalar {k r a x y : ℝ}
    (hk : 0 < k) (hr : 0 < r) (ha : 0 < a)
    (hbasic : k * x ≤ a - 1)
    (hcontract : y ≤ x / (r ^ 2 * a)) :
    k * y ≤ 1 / r ^ 2 := by
  have hden : 0 < r ^ 2 * a := by positivity
  have hmul := mul_le_mul_of_nonneg_left
    ((le_div_iff₀ hden).mp hcontract) hk.le
  have hfirst : k * y ≤ (a - 1) / (r ^ 2 * a) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hmul, hbasic]
  calc
    k * y ≤ (a - 1) / (r ^ 2 * a) := hfirst
    _ ≤ a / (r ^ 2 * a) := div_le_div_of_nonneg_right (by linarith) hden.le
    _ = 1 / r ^ 2 := by field_simp [ha.ne', hr.ne']

/-- A scaled squared-distance bound gives the exact entropy deficit. -/
theorem entropy_of_scaled_hilbertSchmidt (σ : MState d)
    (ε : ℝ) (hε : 0 ≤ ε) (hd : 0 < (Fintype.card d : ℝ))
    (hHS : (Fintype.card d : ℝ) *
      ‖σ.M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 ≤ ε) :
    Real.log (Fintype.card d) - Real.log (1 + ε) ≤ Sᵥₙ σ := by
  have hnorm : ‖σ.M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 ≤
      (ε * (Fintype.card d : ℝ)) / (Fintype.card d : ℝ) ^ 2 := by
    have h : ‖σ.M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 ≤
        ε / (Fintype.card d : ℝ) :=
      (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hHS)
    convert h using 1 <;> field_simp [hd.ne']
  have h := single_copy_of_hilbertSchmidt σ
    (ε * (Fintype.card d : ℝ)) (by positivity) hd hnorm
  simpa only [mul_div_cancel_right₀ ε hd.ne'] using h

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual unital linear postprocessing transfers the trace-zero contraction
to the centered output states. -/
theorem centered_contraction
    (R : HermitianMat d ℂ →ₗ[ℝ] HermitianMat d ℂ)
    (hRone : R 1 = 1)
    (Φ Λ : MState n → MState d)
    (hΛ : ∀ ρ, (Λ ρ).M = R (Φ ρ).M)
    (r a : ℝ) (hd : 0 < (Fintype.card d : ℝ))
    (hR : ∀ Y : HermitianMat d ℂ, Y.trace = 0 →
      ‖R Y‖ ^ 2 ≤ ‖Y‖ ^ 2 / (r ^ 2 * a))
    (ρ : MState n) :
    ‖(Λ ρ).M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 ≤
      ‖(Φ ρ).M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 /
        (r ^ 2 * a) := by
  have htr : ((Φ ρ).M - (Fintype.card d : ℝ)⁻¹ •
      (1 : HermitianMat d ℂ)).trace = 0 := by
    simp [HermitianMat.trace_sub, HermitianMat.trace_smul,
      HermitianMat.trace_one, (Φ ρ).tr, hd.ne']
  simpa only [map_sub, map_smul, hRone, ← hΛ ρ] using hR _ htr

/-- The pointwise squared Hilbert--Schmidt estimate after randomization. -/
theorem smoothed_hilbertSchmidt
    (R : HermitianMat d ℂ →ₗ[ℝ] HermitianMat d ℂ)
    (hRone : R 1 = 1)
    (Φ Λ : MState n → MState d)
    (hΛ : ∀ ρ, (Λ ρ).M = R (Φ ρ).M)
    (r a : ℝ) (hr : 0 < r) (ha : 0 < a)
    (hd : 0 < (Fintype.card d : ℝ))
    (hR : ∀ Y : HermitianMat d ℂ, Y.trace = 0 →
      ‖R Y‖ ^ 2 ≤ ‖Y‖ ^ 2 / (r ^ 2 * a))
    (hbasic : ∀ ρ, (Fintype.card d : ℝ) *
      ‖(Φ ρ).M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 ≤ a - 1)
    (ρ : MState n) :
    (Fintype.card d : ℝ) *
      ‖(Λ ρ).M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 ≤
        1 / r ^ 2 := by
  exact smoothing_scalar hd hr ha (hbasic ρ)
    (centered_contraction R hRone Φ Λ hΛ r a hd hR ρ)

/-- The main proof's one-copy entropy bound for the actual composite map. -/
theorem smoothed_minimumOutputEntropy [Nonempty n]
    (R : HermitianMat d ℂ →ₗ[ℝ] HermitianMat d ℂ)
    (hRone : R 1 = 1)
    (Φ Λ : MState n → MState d)
    (hΛ : ∀ ρ, (Λ ρ).M = R (Φ ρ).M)
    (r a : ℝ) (hr : 0 < r) (ha : 0 < a)
    (hd : 0 < (Fintype.card d : ℝ))
    (hR : ∀ Y : HermitianMat d ℂ, Y.trace = 0 →
      ‖R Y‖ ^ 2 ≤ ‖Y‖ ^ 2 / (r ^ 2 * a))
    (hbasic : ∀ ρ, (Fintype.card d : ℝ) *
      ‖(Φ ρ).M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 ≤ a - 1) :
    Real.log (Fintype.card d) - Real.log (1 + 1 / r ^ 2) ≤
      minimumOutputEntropy Λ := by
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨ρ, rfl⟩
  exact entropy_of_scaled_hilbertSchmidt (Λ ρ) (1 / r ^ 2) (by positivity) hd
    (smoothed_hilbertSchmidt R hRone Φ Λ hΛ r a hr ha hd hR hbasic ρ)

/-- Matrix-entry form for actual CPTP postprocessing. This is the interface
used by the explicit finite-field Pauli construction. -/
theorem cptp_smoothed_hilbertSchmidt
    (R : CPTPMap d d) (Φ : CPTPMap n d)
    (hRone : R.map 1 = 1)
    (r a : ℝ) (hr : 0 < r) (ha : 0 < a)
    (hd : 0 < (Fintype.card d : ℝ))
    (hR : ∀ Y : Matrix d d ℂ, Y.trace = 0 →
      (∑ i, ∑ j, ‖R.map Y i j‖ ^ 2) ≤
        (∑ i, ∑ j, ‖Y i j‖ ^ 2) / (r ^ 2 * a))
    (hbasic : ∀ ρ, (Fintype.card d : ℝ) *
      ‖(Φ ρ).M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 ≤ a - 1)
    (ρ : MState n) :
    (Fintype.card d : ℝ) *
      ‖((R ∘ₘ Φ) ρ).M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 ≤
        1 / r ^ 2 := by
  let RH : HermitianMat d ℂ →ₗ[ℝ] HermitianMat d ℂ :=
    { toFun := R.toHPMap
      map_add' := map_add R.toHPMap
      map_smul' := fun c Y ↦ map_smul R.toHPMap c Y }
  have hRHone : RH 1 = 1 := by
    apply HermitianMat.ext
    exact hRone
  have hRH : ∀ Y : HermitianMat d ℂ, Y.trace = 0 →
      ‖RH Y‖ ^ 2 ≤ ‖Y‖ ^ 2 / (r ^ 2 * a) := by
    intro Y hY
    rw [norm_sq_eq_entry_sum, norm_sq_eq_entry_sum]
    exact hR Y.mat ((HermitianMat.trace_eq_zero_iff Y).mp hY)
  exact smoothed_hilbertSchmidt RH hRHone Φ (R ∘ₘ Φ) (fun _ ↦ rfl)
    r a hr ha hd hRH hbasic ρ

/-- Pointwise entropy of the actual randomized channel. -/
theorem cptp_smoothed_entropy
    (R : CPTPMap d d) (Φ : CPTPMap n d)
    (hRone : R.map 1 = 1)
    (r a : ℝ) (hr : 0 < r) (ha : 0 < a)
    (hd : 0 < (Fintype.card d : ℝ))
    (hR : ∀ Y : Matrix d d ℂ, Y.trace = 0 →
      (∑ i, ∑ j, ‖R.map Y i j‖ ^ 2) ≤
        (∑ i, ∑ j, ‖Y i j‖ ^ 2) / (r ^ 2 * a))
    (hbasic : ∀ ρ, (Fintype.card d : ℝ) *
      ‖(Φ ρ).M - (Fintype.card d : ℝ)⁻¹ • (1 : HermitianMat d ℂ)‖ ^ 2 ≤ a - 1)
    (ρ : MState n) :
    Real.log (Fintype.card d) - Real.log (1 + 1 / r ^ 2) ≤ Sᵥₙ ((R ∘ₘ Φ) ρ) :=
  entropy_of_scaled_hilbertSchmidt _ _ (by positivity) hd
    (cptp_smoothed_hilbertSchmidt R Φ hRone r a hr ha hd hR hbasic ρ)

end MainSmoothing

#print axioms MainSmoothing.smoothed_minimumOutputEntropy
