import QuantumInfo.ForMathlib.HermitianMat.LogExp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # A. Functional calculus for two nested orthogonal projections

This standalone verification module proves the matrix logarithm identity used
for the three-block comparison state in the Bell-output entropy bound.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace EntropyVerification

open HermitianMat
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma nested_square (P E : HermitianMat d ℂ)
    (hP : P.mat * P.mat = P.mat) (hE : E.mat * E.mat = E.mat)
    (hPE : P.mat * E.mat = E.mat) (hEP : E.mat * P.mat = E.mat) :
    (P + E) ^ 2 = P + (3 : ℝ) • E := by
  apply HermitianMat.ext
  simp only [mat_pow, mat_add, mat_smul, pow_two, add_mul, mul_add,
    hP, hE, hPE, hEP]
  module

private lemma nested_cube (P E : HermitianMat d ℂ)
    (hP : P.mat * P.mat = P.mat) (hE : E.mat * E.mat = E.mat)
    (hPE : P.mat * E.mat = E.mat) (hEP : E.mat * P.mat = E.mat) :
    (P + E) ^ 3 = P + (7 : ℝ) • E := by
  have h2 := congrArg HermitianMat.mat (nested_square P E hP hE hPE hEP)
  simp only [mat_pow, mat_add, mat_smul] at h2
  apply HermitianMat.ext
  simp only [mat_pow, mat_add, mat_smul]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2]
  simp only [add_mul, mul_add, Matrix.smul_mul, hP, hE, hPE, hEP]
  module

private lemma nested_spectrum (P E : HermitianMat d ℂ)
    (hP : P.mat * P.mat = P.mat) (hE : E.mat * E.mat = E.mat)
    (hPE : P.mat * E.mat = E.mat) (hEP : E.mat * P.mat = E.mat)
    {x : ℝ} (hx : x ∈ spectrum ℝ (P + E).mat) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  have hp : (P + E).cfc (fun x : ℝ => x ^ 3 - 3 * x ^ 2 + 2 * x) =
      (P + E).cfc (fun _ : ℝ => 0) := by
    rw [HermitianMat.cfc_add_apply, HermitianMat.cfc_sub_apply, HermitianMat.cfc_const_mul, HermitianMat.cfc_const_mul,
      HermitianMat.cfc_pow, HermitianMat.cfc_pow, HermitianMat.cfc_id', HermitianMat.cfc_const]
    rw [nested_square P E hP hE hPE hEP, nested_cube P E hP hE hPE hEP]
    module
  have hp' := (HermitianMat.cfc_eq_cfc_iff_eqOn (A := P + E)
    (fun x : ℝ => x ^ 3 - 3 * x ^ 2 + 2 * x) (fun _ : ℝ => 0)).mp hp hx
  have hfactor : x * (x - 1) * (x - 2) = 0 := by nlinarith [hp']
  rcases mul_eq_zero.mp hfactor with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

private lemma nested_cfc_P (P E : HermitianMat d ℂ)
    (hP : P.mat * P.mat = P.mat) (hE : E.mat * E.mat = E.mat)
    (hPE : P.mat * E.mat = E.mat) (hEP : E.mat * P.mat = E.mat) :
    (P + E).cfc (fun x : ℝ => (3 / 2) * x - (1 / 2) * x ^ 2) = P := by
  rw [HermitianMat.cfc_sub_apply, HermitianMat.cfc_const_mul, HermitianMat.cfc_const_mul, HermitianMat.cfc_id', HermitianMat.cfc_pow,
    nested_square P E hP hE hPE hEP]
  module

private lemma nested_cfc_E (P E : HermitianMat d ℂ)
    (hP : P.mat * P.mat = P.mat) (hE : E.mat * E.mat = E.mat)
    (hPE : P.mat * E.mat = E.mat) (hEP : E.mat * P.mat = E.mat) :
    (P + E).cfc (fun x : ℝ => (1 / 2) * x ^ 2 - (1 / 2) * x) = E := by
  rw [HermitianMat.cfc_sub_apply, HermitianMat.cfc_const_mul, HermitianMat.cfc_const_mul, HermitianMat.cfc_id', HermitianMat.cfc_pow,
    nested_square P E hP hE hPE hEP]
  module

private lemma nested_cfc_linear (P E : HermitianMat d ℂ)
    (hP : P.mat * P.mat = P.mat) (hE : E.mat * E.mat = E.mat)
    (hPE : P.mat * E.mat = E.mat) (hEP : E.mat * P.mat = E.mat)
    (a b c : ℝ) :
    (P + E).cfc (fun x : ℝ => a + b * ((3 / 2) * x - (1 / 2) * x ^ 2) +
      c * ((1 / 2) * x ^ 2 - (1 / 2) * x)) =
        a • (1 : HermitianMat d ℂ) + b • P + c • E := by
  rw [HermitianMat.cfc_add_apply, HermitianMat.cfc_add_apply, HermitianMat.cfc_const_mul, HermitianMat.cfc_const_mul,
    HermitianMat.cfc_const, nested_cfc_P P E hP hE hPE hEP, nested_cfc_E P E hP hE hPE hEP]

/-- Functional calculus on the three orthogonal blocks `E`, `P-E`, and `1-P`.
The theorem holds for every real function because the matrix spectrum is finite. -/
lemma cfc_nested_projections (P E : HermitianMat d ℂ)
    (hP : P.mat * P.mat = P.mat) (hE : E.mat * E.mat = E.mat)
    (hPE : P.mat * E.mat = E.mat) (hEP : E.mat * P.mat = E.mat)
    (a b c : ℝ) (f : ℝ → ℝ) :
    (a • (1 : HermitianMat d ℂ) + b • P + c • E).cfc f =
      f a • (1 : HermitianMat d ℂ) + (f (a + b) - f a) • P +
        (f (a + b + c) - f (a + b)) • E := by
  let p : ℝ → ℝ := fun x => (3 / 2) * x - (1 / 2) * x ^ 2
  let e : ℝ → ℝ := fun x => (1 / 2) * x ^ 2 - (1 / 2) * x
  have hp : (P + E).cfc p = P := nested_cfc_P P E hP hE hPE hEP
  have he : (P + E).cfc e = E := nested_cfc_E P E hP hE hPE hEP
  have hlinear (u v w : ℝ) :
      (P + E).cfc (fun x => u + v * p x + w * e x) =
        u • (1 : HermitianMat d ℂ) + v • P + w • E := by
    rw [HermitianMat.cfc_add_apply, HermitianMat.cfc_add_apply, HermitianMat.cfc_const_mul, HermitianMat.cfc_const_mul,
      HermitianMat.cfc_const, hp, he]
  rw [← hlinear a b c, ← HermitianMat.cfc_comp_apply,
    ← hlinear (f a) (f (a + b) - f a) (f (a + b + c) - f (a + b))]
  apply HermitianMat.cfc_congr
  intro x hx
  rcases nested_spectrum P E hP hE hPE hEP hx with rfl | rfl | rfl
  all_goals norm_num [p, e]

/-- The logarithm of a scalar linear combination of two nested projections. -/
lemma log_nested_projections (P E : HermitianMat d ℂ)
    (hP : P.mat * P.mat = P.mat) (hE : E.mat * E.mat = E.mat)
    (hPE : P.mat * E.mat = E.mat) (hEP : E.mat * P.mat = E.mat)
    (a b c : ℝ) :
    (a • (1 : HermitianMat d ℂ) + b • P + c • E).log =
      Real.log a • (1 : HermitianMat d ℂ) +
        (Real.log (a + b) - Real.log a) • P +
        (Real.log (a + b + c) - Real.log (a + b)) • E := by
  exact cfc_nested_projections P E hP hE hPE hEP a b c Real.log

/-- Positivity of the three block eigenvalues implies positive definiteness. -/
lemma posDef_nested_projections (P E : HermitianMat d ℂ)
    (hP : P.mat * P.mat = P.mat) (hE : E.mat * E.mat = E.mat)
    (hPE : P.mat * E.mat = E.mat) (hEP : E.mat * P.mat = E.mat)
    (a b c : ℝ) (ha : 0 < a) (hab : 0 < a + b) (habc : 0 < a + b + c) :
    (a • (1 : HermitianMat d ℂ) + b • P + c • E).mat.PosDef := by
  rw [← nested_cfc_linear P E hP hE hPE hEP a b c]
  apply (HermitianMat.cfc_posDef _ _).2
  intro i
  have hx := nested_spectrum P E hP hE hPE hEP
    ((P + E).H.eigenvalues_mem_spectrum_real i)
  rcases hx with hx | hx | hx
  all_goals
    norm_num [hx]
    assumption

/-- The trace of the three-block comparison operator, using the projection ranks. -/
lemma trace_nested_projections (P E : HermitianMat d ℂ) (k a b c : ℝ)
    (hP : P.trace = k) (hE : E.trace = 1) :
    (a • (1 : HermitianMat d ℂ) + b • P + c • E).trace =
      a * Fintype.card d + b * k + c := by
  simp [hP, hE]

end EntropyVerification
