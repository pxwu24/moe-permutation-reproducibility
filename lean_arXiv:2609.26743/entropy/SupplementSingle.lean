import SingleChannel

/-!
# Supplement, Lemma 3: the pointwise Hilbert–Schmidt estimate

`single_copy_hilbertSchmidt_bound` is (S4), for every density matrix input.
The only analytic premise is (S3).  The entry equation specifies the channel
(S1), through its adjoint matrices `suppressorK`; no norm or entropy conclusion
is assumed.  The matrix norm in (S3) is the Euclidean operator norm, while the
norm on `HermitianMat` in (S4) is the unnormalized Hilbert–Schmidt norm.

The result permits nonnegative `C` and `γ`, so in particular it applies under
the paper's assumptions `C > 0` and `0 < γ < 1`.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
open EntropyLemmas.BellAlgebra SuppressorEntropy

namespace SupplementSingle

variable {n k : ℕ}

/-- The self-pairing estimate in the proof of Lemma 3. -/
theorem single_copy_self_pairing
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (Φ : MState (Fin n) → MState (Fin k))
    (hΦ : ∀ ρ i j, (Φ ρ).m i j = channelEntry (suppressorK H U) ρ.m i j)
    (C γ : ℝ) (hk : 0 < k)
    (hbound : ∀ W : HermitianMat (Fin k) ℂ, (∀ i, W i i = 0) →
      ‖testObservable H U W‖ ≤ C * γ * ‖W‖)
    (ρ : MState (Fin n)) :
    (k : ℝ) * ‖(Φ ρ).M - (k : ℝ)⁻¹ • (1 : HermitianMat (Fin k) ℂ)‖ ^ 2 ≤
      C * γ * ‖(Φ ρ).M - (k : ℝ)⁻¹ • (1 : HermitianMat (Fin k) ℂ)‖ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let X : HermitianMat (Fin k) ℂ := (Φ ρ).M - (k : ℝ)⁻¹ • 1
  have hXdiag : ∀ i, X i i = 0 := by
    intro i
    have hd := suppressor_output_diagonal H U hU Φ hΦ ρ i
    change (Φ ρ).m i i - ((k : ℝ)⁻¹ : ℝ) •
      (1 : Matrix (Fin k) (Fin k) ℂ) i i = 0
    simp [hd]
  have hXtr : X.trace = 0 := by
    simp [X, HermitianMat.trace_sub, HermitianMat.trace_smul,
      HermitianMat.trace_one, ne_of_gt hkR]
  have hself : inner ℝ (Φ ρ).M X = ‖X‖ ^ 2 := by
    have hx : (Φ ρ).M = X + (k : ℝ)⁻¹ • (1 : HermitianMat (Fin k) ℂ) := by
      dsimp [X]
      abel
    rw [hx]
    simp [inner_add_left, inner_smul_left, HermitianMat.one_inner, hXtr]
  let B : HermitianMat (Fin n) ℂ :=
    ⟨testObservable H U X, testObservable_isHermitian H hH U X⟩
  have hp := channelEntry_tracePairing (suppressorK H U) ρ.m X.mat
  have hm : Matrix.of (fun i j ↦ channelEntry (suppressorK H U) ρ.m i j) =
      (Φ ρ).m := by
    funext i j
    exact (hΦ ρ i j).symm
  rw [hm, suppressorK_zeroDiagonal_sum H U X.mat hXdiag] at hp
  have hpR := congrArg Complex.re hp
  have hp' : inner ℝ (Φ ρ).M X = inner ℝ ρ.M B / (k : ℝ) := by
    rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
    change ((Φ ρ).m * X.mat).trace.re =
      (ρ.m * testObservable H U X).trace.re / (k : ℝ)
    simpa only [Complex.div_natCast_re, HermitianMat.mat_apply, testObservable] using hpR
  have hpair : (k : ℝ) * ‖X‖ ^ 2 = inner ℝ ρ.M B := by
    rw [hself] at hp'
    exact (mul_comm _ _).trans ((eq_div_iff hkR.ne').mp hp')
  have hle := (state_inner_le_operatorNorm ρ B).trans (hbound X hXdiag)
  exact hpair.le.trans hle

/-- Supplement (S4): every output is close to the maximally mixed state in
squared Hilbert–Schmidt norm, under precisely the sandwich estimate (S3). -/
theorem single_copy_hilbertSchmidt_bound
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (Φ : MState (Fin n) → MState (Fin k))
    (hΦ : ∀ ρ i j, (Φ ρ).m i j = channelEntry (suppressorK H U) ρ.m i j)
    (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hk : 0 < k)
    (hbound : ∀ W : HermitianMat (Fin k) ℂ, (∀ i, W i i = 0) →
      ‖testObservable H U W‖ ≤ C * γ * ‖W‖)
    (ρ : MState (Fin n)) :
    ‖(Φ ρ).M - (k : ℝ)⁻¹ • (1 : HermitianMat (Fin k) ℂ)‖ ^ 2 ≤
      C ^ 2 * γ ^ 2 / (k : ℝ) ^ 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpair := single_copy_self_pairing H hH U hU Φ hΦ C γ hk hbound ρ
  have hsq := hilbertSchmidt_bound_from_self_pairing
    (norm_nonneg ((Φ ρ).M - (k : ℝ)⁻¹ • (1 : HermitianMat (Fin k) ℂ)))
    (mul_nonneg hC hγ) hkR hpair
  simpa only [mul_pow] using hsq

/-- Supplement Lemma 3, combining (S4) and the entropy consequence (S5). -/
theorem lemma3 [Nonempty (Fin n)]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (Φ : MState (Fin n) → MState (Fin k))
    (hΦ : ∀ ρ i j, (Φ ρ).m i j = channelEntry (suppressorK H U) ρ.m i j)
    (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hk : 0 < k)
    (hbound : ∀ W : HermitianMat (Fin k) ℂ, (∀ i, W i i = 0) →
      ‖testObservable H U W‖ ≤ C * γ * ‖W‖) :
    (∀ ρ : MState (Fin n),
      ‖(Φ ρ).M - (k : ℝ)⁻¹ • (1 : HermitianMat (Fin k) ℂ)‖ ^ 2 ≤
        C ^ 2 * γ ^ 2 / (k : ℝ) ^ 2) ∧
      Real.log k - Real.log (1 + C ^ 2 * γ ^ 2 / k) ≤ minimumOutputEntropy Φ := by
  exact ⟨single_copy_hilbertSchmidt_bound H hH U hU Φ hΦ C γ hC hγ hk hbound,
    single_copy_lemma H hH U hU Φ hΦ C γ hC hγ hk hbound⟩

#print axioms single_copy_self_pairing
#print axioms single_copy_hilbertSchmidt_bound
#print axioms lemma3

end SupplementSingle
