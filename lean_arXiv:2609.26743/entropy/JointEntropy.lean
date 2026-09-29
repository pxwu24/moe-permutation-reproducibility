import QuantumInfo.Entropy.VonNeumann
import QuantumInfo.ForMathlib.HermitianMat.Peierls
import JointProjection

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ComplexOrder RealInnerProductSpace
open HermitianMat

namespace SuppressorEntropy

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The entropy tangent inequality, including the zero-probability endpoint. -/
theorem negMulLog_le_tangent {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) :
    Real.negMulLog p ≤ -p * Real.log r + r - p := by
  rcases eq_or_lt_of_le hp with h | hp
  · subst p
    simpa [Real.negMulLog] using hr.le
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hr hp)
    rw [Real.log_div hr.ne' hp.ne'] at hlog
    have h := mul_le_mul_of_nonneg_left hlog hp.le
    have hdiv : p * (r / p) = r := by field_simp [hp.ne']
    dsimp [Real.negMulLog]
    nlinarith

/-- A state diagonal, after a unitary change of basis. -/
def basisDiagonal (σ : MState d) (U : Matrix.unitaryGroup d ℂ) (i : d) : ℝ :=
  ((σ.M.conj U.val).mat i i).re

theorem basisDiagonal_nonneg (σ : MState d) (U : Matrix.unitaryGroup d ℂ) (i : d) :
    0 ≤ basisDiagonal σ U i := by
  have hA : 0 ≤ σ.M.conj U.val := HermitianMat.conj_nonneg U.val σ.nonneg
  exact (Complex.le_def.mp ((HermitianMat.zero_le_iff.mp hA).diag_nonneg (i := i))).1

theorem sum_basisDiagonal (σ : MState d) (U : Matrix.unitaryGroup d ℂ) :
    ∑ i, basisDiagonal σ U i = 1 := by
  calc
    ∑ i, basisDiagonal σ U i = (σ.M.conj U.val).trace := by
      simp [basisDiagonal, HermitianMat.trace_eq_re_trace, Matrix.trace, HermitianMat.conj, -HermitianMat.mat_apply]
    _ = σ.M.trace := HermitianMat.trace_conj_unitary σ.M U
    _ = 1 := σ.tr

/-- Peierls' inequality gives a fully quantum entropy bound in any unitary basis. -/
theorem entropy_le_basisDiagonal (σ : MState d) (U : Matrix.unitaryGroup d ℂ) :
    Sᵥₙ σ ≤ ∑ i, Real.negMulLog (basisDiagonal σ U i) := by
  let A := σ.M.conj U.val
  have hA : 0 ≤ A := HermitianMat.conj_nonneg U.val σ.nonneg
  have h := HermitianMat.peierls_inequality_ici A (fun x => -Real.negMulLog x)
    Real.strictConcaveOn_negMulLog.concaveOn.neg hA
  have hcfc : (A.cfc (fun x => -Real.negMulLog x)).trace = -Sᵥₙ σ := by
    rw [show (fun x => -Real.negMulLog x) = -Real.negMulLog from rfl,
      HermitianMat.cfc_neg, HermitianMat.trace_neg]
    dsimp [A]
    rw [HermitianMat.trace_cfc_conj_unitary, Sᵥₙ_eq_trace_cfc_negMulLog]
  rw [hcfc] at h
  simpa [basisDiagonal, A, Finset.sum_neg_distrib] using neg_le_neg h

/-- Cross entropy against any strictly positive finite distribution, derived from
Peierls and the scalar logarithm inequality, with no relative-entropy axioms. -/
theorem entropy_le_crossEntropy (σ : MState d) (U : Matrix.unitaryGroup d ℂ)
    (r : d → ℝ) (hr : ∀ i, 0 < r i) (hrsum : ∑ i, r i = 1) :
    Sᵥₙ σ ≤ -∑ i, basisDiagonal σ U i * Real.log (r i) := by
  apply (entropy_le_basisDiagonal σ U).trans
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    negMulLog_le_tangent (basisDiagonal_nonneg σ U i) (hr i)
  simpa [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    hrsum, sum_basisDiagonal, neg_mul] using h

/-- Klein's entropy upper bound for a faithful comparison state. This proof
uses the preceding Peierls argument, rather than importing relative entropy. -/
theorem entropy_le_neg_inner_log (σ τ : MState d) (hτ : τ.M.mat.PosDef) :
    Sᵥₙ σ ≤ -⟪σ.M, τ.M.log⟫ := by
  let V := τ.M.H.eigenvectorUnitary
  let U : Matrix.unitaryGroup d ℂ := star V
  let r := τ.M.H.eigenvalues
  have hr : ∀ i, 0 < r i := hτ.eigenvalues_pos
  have hrsum : ∑ i, r i = 1 := by
    rw [HermitianMat.sum_eigenvalues_eq_trace]
    exact τ.tr
  have hcross := entropy_le_crossEntropy σ U r hr hrsum
  have hdiag : τ.M.log.conj U.val = HermitianMat.diagonal ℂ (Real.log ∘ r) := by
    have hspec := HermitianMat.eq_conj_diagonal τ.M
    conv_lhs => rw [hspec]
    rw [HermitianMat.log_conj_unitary, HermitianMat.log,
      HermitianMat.cfc_diagonal, HermitianMat.conj_conj]
    simp [U, V, r]
  have heval : ⟪σ.M, τ.M.log⟫ =
      ∑ i, basisDiagonal σ U i * Real.log (r i) := by
    rw [← HermitianMat.inner_conj_unitary σ.M τ.M.log U, hdiag]
    simp [HermitianMat.inner_eq_re_trace, HermitianMat.diagonal,
      Matrix.mul_diagonal, Matrix.trace, basisDiagonal, HermitianMat.conj, -HermitianMat.mat_apply]
  rwa [← heval] at hcross

/-- Entropy comparison from two linear moments and an explicit reference
logarithm. This compares actual quantum entropies, with no entropy hypothesis. -/
theorem entropy_le_of_log_moments (σ τ : MState d) (hτ : τ.M.mat.PosDef)
    (P E : HermitianMat d ℂ) (a b c : ℝ) (hc : 0 ≤ c)
    (hlog : τ.M.log = a • (1 : HermitianMat d ℂ) + b • P + c • E)
    (hP : ⟪σ.M, P⟫ = ⟪τ.M, P⟫) (hE : ⟪τ.M, E⟫ ≤ ⟪σ.M, E⟫) :
    Sᵥₙ σ ≤ Sᵥₙ τ := by
  have hcross := entropy_le_neg_inner_log σ τ hτ
  have hmoment := mul_le_mul_of_nonneg_left hE hc
  rw [Sᵥₙ_eq_neg_trace_log τ, HermitianMat.inner_comm τ.M.log τ.M] 
  rw [hlog] at hcross ⊢
  simp only [HermitianMat.inner_add_right, HermitianMat.inner_smul_right, HermitianMat.inner_one,
    σ.tr, τ.tr, mul_one, hP] at hcross ⊢
  linarith

/-- Direct projection form of the joint-copy entropy estimate. It constructs the
comparison state and proves its entropy formula by finite spectral calculus. -/
theorem entropy_le_bell_projections (σ : MState d)
    (P E : HermitianMat d ℂ)
    (hP : P.mat * P.mat = P.mat) (hE : E.mat * E.mat = E.mat)
    (hPE : P.mat * E.mat = E.mat) (hEP : E.mat * P.mat = E.mat)
    (k : ℕ) (hk : 2 ≤ k) (hd : Fintype.card d = k^2)
    (htrP : P.trace = k) (htrE : E.trace = 1)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hmass : ⟪σ.M, P⟫ = 1/(k:ℝ))
    (hq : (1+s*((k:ℝ)-1))/(k:ℝ)^2 ≤ ⟪σ.M, E⟫) :
    Sᵥₙ σ ≤ Real.negMulLog ((1+s*((k:ℝ)-1))/(k:ℝ)^2) +
      ((k:ℝ)-1)*Real.negMulLog ((1-s)/(k:ℝ)^2) +
      ((k:ℝ)*((k:ℝ)-1))*Real.negMulLog (1/(k:ℝ)^2) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1:ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  let a : ℝ := 1/(k:ℝ)^2
  let b : ℝ := -s/(k:ℝ)^2
  let c : ℝ := s/(k:ℝ)
  have hab : a+b = (1-s)/(k:ℝ)^2 := by dsimp [a,b]; ring
  have habc : a+b+c = (1+s*((k:ℝ)-1))/(k:ℝ)^2 := by
    dsimp [a,b,c]
    field_simp [hk0.ne']
    ring
  have ha : 0 < a := by dsimp [a]; positivity
  have habpos : 0 < a+b := by rw [hab]; positivity
  have habcpos : 0 < a+b+c := by rw [habc]; positivity
  let T : HermitianMat d ℂ := a • 1 + b • P + c • E
  have hTpos : T.mat.PosDef :=
    EntropyVerification.posDef_nested_projections P E hP hE hPE hEP a b c
      ha habpos habcpos
  have hTtr : T.trace = 1 := by
    dsimp [T]
    rw [EntropyVerification.trace_nested_projections P E (k:ℝ) a b c htrP htrE, hd]
    dsimp [a,b,c]
    push_cast
    field_simp [hk0.ne']
    ring
  let τ : MState d := {
    M := T
    nonneg := HermitianMat.zero_le_iff.mpr hTpos.posSemidef
    tr := hTtr }
  have hPP : ⟪P,P⟫ = (k:ℝ) := by
    rw [HermitianMat.inner_eq_re_trace, hP, ← HermitianMat.trace_eq_re_trace, htrP]
  have hEE : ⟪E,E⟫ = (1:ℝ) := by
    rw [HermitianMat.inner_eq_re_trace, hE, ← HermitianMat.trace_eq_re_trace, htrE]
  have hPE' : ⟪P,E⟫ = (1:ℝ) := by
    rw [HermitianMat.inner_eq_re_trace, hPE, ← HermitianMat.trace_eq_re_trace, htrE]
  have hEP' : ⟪E,P⟫ = (1:ℝ) := by rw [HermitianMat.inner_comm]; exact hPE'
  have hτP : ⟪τ.M,P⟫ = 1/(k:ℝ) := by
    change ⟪a • (1 : HermitianMat d ℂ) + b • P + c • E,P⟫ = _
    simp only [HermitianMat.inner_add_left, HermitianMat.inner_smul_left, HermitianMat.one_inner,
      htrP, hPP, hEP', mul_one]
    dsimp [a,b,c]
    field_simp [hk0.ne']
    ring
  have hτE : ⟪τ.M,E⟫ = (1+s*((k:ℝ)-1))/(k:ℝ)^2 := by
    change ⟪a • (1 : HermitianMat d ℂ) + b • P + c • E,E⟫ = _
    simp only [HermitianMat.inner_add_left, HermitianMat.inner_smul_left, HermitianMat.one_inner,
      htrE, hPE', hEE, mul_one]
    exact habc
  have hcpos : 0 ≤ Real.log (a+b+c) - Real.log (a+b) := by
    apply sub_nonneg.mpr
    apply Real.log_le_log habpos
    dsimp [c]
    linarith [div_pos hs0 hk0]
  have hlog := EntropyVerification.log_nested_projections P E hP hE hPE hEP a b c
  have hentropy : Sᵥₙ σ ≤ Sᵥₙ τ :=
    entropy_le_of_log_moments σ τ hTpos P E
      (Real.log a) (Real.log (a+b)-Real.log a)
      (Real.log (a+b+c)-Real.log (a+b)) hcpos hlog
      (hmass.trans hτP.symm) (by rw [hτE]; exact hq)
  apply hentropy.trans_eq
  rw [Sᵥₙ_eq_trace_cfc_negMulLog]
  change (T.cfc Real.negMulLog).trace = _
  dsimp [T]
  rw [EntropyVerification.cfc_nested_projections P E hP hE hPE hEP a b c,
    HermitianMat.trace_add, HermitianMat.trace_add,
    HermitianMat.trace_smul, HermitianMat.trace_smul, HermitianMat.trace_smul,
    HermitianMat.trace_one, htrP, htrE, hd, habc, hab]
  dsimp [a]
  push_cast
  ring

end SuppressorEntropy
