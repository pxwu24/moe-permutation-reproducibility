import QuantumInfo.Entropy.VonNeumann

/-!
The single-copy entropy estimate for an actual finite-dimensional quantum state.
All norms on `HermitianMat` below are the unnormalized Hilbert--Schmidt norm.
The logarithm is the natural logarithm.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
open scoped BigOperators RealInnerProductSpace

namespace SuppressorEntropy

variable {d : Type*} [Fintype d]

/-- A probability vector has strictly positive collision probability. -/
theorem sum_sq_pos_of_probability (p : d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    0 < ∑ i, (p i)^2 := by
  have hex : ∃ i, 0 < p i := by
    by_contra! h
    have hle : ∑ i, p i ≤ 0 := Finset.sum_nonpos (fun i _ ↦ h i)
    linarith
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ ↦ pow_nonneg (hp j) 2)
    ⟨i, Finset.mem_univ i, sq_pos_of_pos hi⟩

/-- Shannon entropy dominates collision entropy, including zero probabilities. -/
theorem neg_log_sum_sq_le_entropy (p : d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    -Real.log (∑ i, (p i)^2) ≤ ∑ i, Real.negMulLog (p i) := by
  let Q := ∑ i, (p i)^2
  have hQ : 0 < Q := sum_sq_pos_of_probability p hp hsum
  have hpoint : ∀ i,
      p i * (Real.log (p i) - Real.log Q) ≤ (p i)^2 / Q - p i := by
    intro i
    by_cases hi : p i = 0
    · simp [hi]
    · have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hi)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hpi hQ)
      rw [Real.log_div hi hQ.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (hp i)
      calc
        p i * (Real.log (p i) - Real.log Q) ≤ p i * (p i / Q - 1) := hmul
        _ = (p i)^2 / Q - p i := by ring
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hpoint i)
  have hright : ∑ i, ((p i)^2 / Q - p i) = 0 := by
    simp only [div_eq_mul_inv, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
    change Q * Q⁻¹ - 1 = 0
    rw [mul_inv_cancel₀ hQ.ne', sub_self]
  have hleft : ∑ i, p i * (Real.log (p i) - Real.log Q) =
      (∑ i, p i * Real.log (p i)) - Real.log Q := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [hright, hleft] at htotal
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  change -Real.log Q ≤ -(∑ i, p i * Real.log (p i))
  linarith

/-- The Shannon/collision comparison for the library's probability distribution. -/
theorem neg_log_collision_le_shannon (p : ProbDistribution d) :
    -Real.log (∑ i, (p i : ℝ)^2) ≤ Hₛ p := by
  simpa only [Hₛ, H₁, ProbDistribution.prob] using
    neg_log_sum_sq_le_entropy (fun i ↦ (p i : ℝ))
      (fun i ↦ (p i).zero_le_coe) p.normalized

variable [DecidableEq d]

/-- Collision entropy lower-bounds the von Neumann entropy of an actual state. -/
theorem neg_log_purity_le_vonNeumann (σ : MState d) :
    -Real.log (‖σ.M‖^2) ≤ Sᵥₙ σ := by
  have hEq : ‖σ.M‖^2 = ∑ i, (σ.spectrum i : ℝ)^2 := by
    simpa [MState.spectrum, ProbDistribution.mk'] using
      HermitianMat.norm_eq_sum_eigenvalues_sq σ.M
  rw [hEq]
  exact neg_log_collision_le_shannon σ.spectrum

/-- The Hilbert--Schmidt norm squared of a state is strictly positive. -/
theorem state_purity_pos (σ : MState d) : 0 < ‖σ.M‖^2 := by
  rw [HermitianMat.norm_eq_sum_eigenvalues_sq]
  exact sum_sq_pos_of_probability _ (σ.psd.eigenvalues_nonneg ·)
    (by rw [HermitianMat.sum_eigenvalues_eq_trace, σ.tr])

/-- Exact orthogonal decomposition of purity around the maximally mixed state. -/
theorem norm_sub_uniform_sq (σ : MState d)
    (hk : 0 < (Fintype.card d : ℝ)) :
    ‖σ.M - ((Fintype.card d : ℝ)⁻¹) • (1 : HermitianMat d ℂ)‖^2 =
      ‖σ.M‖^2 - (Fintype.card d : ℝ)⁻¹ := by
  simp only [← real_inner_self_eq_norm_sq, HermitianMat.inner_sub_left,
    HermitianMat.inner_sub_right, HermitianMat.inner_smul_left,
    HermitianMat.inner_smul_right, HermitianMat.inner_one, HermitianMat.one_inner,
    HermitianMat.trace_sub, HermitianMat.trace_smul, σ.tr, HermitianMat.trace_one]
  field_simp [ne_of_gt hk]
  ring

/-- The requested single-copy bound, once the Hilbert--Schmidt estimate is given. -/
theorem single_copy_of_hilbertSchmidt (σ : MState d)
    (a : ℝ) (ha : 0 ≤ a) (hk : 0 < (Fintype.card d : ℝ))
    (hHS : ‖σ.M - ((Fintype.card d : ℝ)⁻¹) • (1 : HermitianMat d ℂ)‖^2
      ≤ a / (Fintype.card d : ℝ)^2) :
    Real.log (Fintype.card d) - Real.log (1 + a / (Fintype.card d)) ≤ Sᵥₙ σ := by
  let k : ℝ := Fintype.card d
  have hk' : 0 < k := hk
  have hb : 0 < 1 + a / k := by positivity
  have hpur : ‖σ.M‖^2 ≤ (1 + a / k) / k := by
    rw [norm_sub_uniform_sq σ hk] at hHS
    have halg : (1 + a / k) / k = k⁻¹ + a / k^2 := by
      field_simp [ne_of_gt hk']
    rw [halg]
    change ‖σ.M‖^2 - k⁻¹ ≤ a / k^2 at hHS
    linarith
  have hlog := Real.log_le_log (state_purity_pos σ) hpur
  rw [Real.log_div hb.ne' hk'.ne'] at hlog
  have hent := neg_log_purity_le_vonNeumann σ
  change Real.log k - Real.log (1 + a / k) ≤ Sᵥₙ σ
  linarith

/-- The elementary division in the Hilbert--Schmidt duality argument. -/
theorem hilbertSchmidt_bound_from_self_pairing
    {x b k : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) (hk : 0 < k)
    (h : k * x^2 ≤ b * x) : x^2 ≤ b^2 / k^2 := by
  have hxle : x ≤ b / k := by
    by_cases hx0 : x = 0
    · subst x; positivity
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      apply (le_div_iff₀ hk).2
      apply (mul_le_mul_iff_right₀ hxpos).mp
      nlinarith only [h]
  have hsq := sq_le_sq₀ hx (div_nonneg hb hk.le) |>.2 hxle
  simpa only [div_pow] using hsq

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Minimum output von Neumann entropy; this definition also applies to any
state-valued map, without needing a particular bundled channel representation. -/
def minimumOutputEntropy (Φ : MState n → MState d) : ℝ :=
  sInf (Set.range (fun ρ ↦ Sᵥₙ (Φ ρ)))

/-- Evaluating any input state supplies an upper bound on minimum output entropy. -/
theorem minimumOutputEntropy_le (Φ : MState n → MState d) (ρ : MState n) :
    minimumOutputEntropy Φ ≤ Sᵥₙ (Φ ρ) := by
  apply csInf_le
  · exact ⟨0, by rintro x ⟨σ, rfl⟩; exact Sᵥₙ_nonneg (Φ σ)⟩
  · exact ⟨ρ, rfl⟩

/-- The single-copy minimum-output entropy conclusion for all output states. -/
theorem minimumOutputEntropy_lower_of_hilbertSchmidt [Nonempty n]
    (Φ : MState n → MState d) (a : ℝ) (ha : 0 ≤ a)
    (hk : 0 < (Fintype.card d : ℝ))
    (hHS : ∀ ρ, ‖(Φ ρ).M - ((Fintype.card d : ℝ)⁻¹) •
      (1 : HermitianMat d ℂ)‖^2 ≤ a / (Fintype.card d : ℝ)^2) :
    Real.log (Fintype.card d) - Real.log (1 + a / (Fintype.card d)) ≤
      minimumOutputEntropy Φ := by
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨ρ, rfl⟩
  exact single_copy_of_hilbertSchmidt (Φ ρ) a ha hk (hHS ρ)

/-- A convenient formulation using precisely the self-pairing inequality
obtained by testing the dual estimate on the centered output matrix. -/
theorem minimumOutputEntropy_lower_of_self_pairing [Nonempty n]
    (Φ : MState n → MState d) (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hk : 0 < (Fintype.card d : ℝ))
    (hpair : ∀ ρ, (Fintype.card d : ℝ) *
      ‖(Φ ρ).M - ((Fintype.card d : ℝ)⁻¹) • (1 : HermitianMat d ℂ)‖^2 ≤
      (C * γ) * ‖(Φ ρ).M - ((Fintype.card d : ℝ)⁻¹) •
        (1 : HermitianMat d ℂ)‖) :
    Real.log (Fintype.card d) -
      Real.log (1 + C^2 * γ^2 / (Fintype.card d)) ≤ minimumOutputEntropy Φ := by
  apply minimumOutputEntropy_lower_of_hilbertSchmidt Φ (C^2 * γ^2) (by positivity) hk
  intro ρ
  simpa only [mul_pow] using hilbertSchmidt_bound_from_self_pairing
    (norm_nonneg _) (mul_nonneg hC hγ) hk (hpair ρ)

end SuppressorEntropy

#print axioms SuppressorEntropy.single_copy_of_hilbertSchmidt
#print axioms SuppressorEntropy.minimumOutputEntropy_lower_of_self_pairing
#print axioms SuppressorEntropy.minimumOutputEntropy_le
