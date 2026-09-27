import FiniteFilterSupport
import Mathlib.Algebra.Order.Ring.Pow

/-!
# A. Lower bounds for a finite spectral filter

This standalone verification file proves an actual Loewner-order estimate for
Hermitian matrix families with an isotropic second moment.  The proof lifts a
scalar supporting-line inequality by functional calculus; it does not assume
operator convexity of powers.
-/

noncomputable section
open scoped BigOperators
open ComplexOrder

namespace SignFilterLower

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

/-- The scalar supporting line for a positive integral power. -/
lemma power_supporting_line (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (L : ℕ) :
    a ^ L + (L : ℝ) * a ^ (L - 1) * (x - a) ≤ x ^ L := by
  simpa only [add_sub_cancel] using
    pow_add_mul_le_add_pow ha (show 0 ≤ 2 * a + (x - a) by linarith) L

/-- Functional calculus turns the scalar supporting line into a matrix inequality. -/
lemma even_power_supporting_line (Z : HermitianMat d ℂ) (a : ℝ)
    (ha : 0 ≤ a) (L : ℕ) :
    a ^ L • (1 : HermitianMat d ℂ) +
      ((L : ℝ) * a ^ (L - 1)) • (Z ^ 2 - a • 1) ≤ Z ^ (2 * L) := by
  have hp : 0 ≤ Z.cfc (fun x => x ^ (2 * L) -
      (a ^ L + (L : ℝ) * a ^ (L - 1) * (x ^ 2 - a))) := by
    rw [HermitianMat.cfc_nonneg_iff]
    intro i
    have hh := power_supporting_line a (Z.H.eigenvalues i ^ 2) ha
      (sq_nonneg _) L
    rw [← pow_mul] at hh
    linarith
  simpa only [HermitianMat.cfc_sub_apply, HermitianMat.cfc_add_apply,
    HermitianMat.cfc_const_mul, HermitianMat.cfc_const,
    HermitianMat.cfc_pow, sub_nonneg] using hp

/-- A finite Hermitian family whose second moment is a scalar matrix has a
corresponding lower bound on every even moment, in Loewner order. -/
lemma even_moment_lower (Z : ι → HermitianMat d ℂ) (a : ℝ)
    (ha : 0 ≤ a) (L : ℕ)
    (hsecond : ∑ i, Z i ^ 2 = ((Fintype.card ι : ℝ) * a) • 1) :
    ((Fintype.card ι : ℝ) * a ^ L) • (1 : HermitianMat d ℂ) ≤
      ∑ i, Z i ^ (2 * L) := by
  have ht := Finset.sum_le_sum fun (i : ι) (_ : i ∈ Finset.univ) =>
    even_power_supporting_line (Z i) a ha L
  have hs : (∑ i, (Z i ^ 2 - a • (1 : HermitianMat d ℂ))) = 0 := by
    rw [Finset.sum_sub_distrib, hsecond, Finset.sum_const]
    simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Finset.card_univ,
      sub_self]
  simpa only [Finset.sum_add_distrib, ← Finset.smul_sum, hs, smul_zero,
    add_zero, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    Finset.card_univ, mul_comm] using ht

section Signs
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A Boolean value encoded as a real sign. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

lemma sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

lemma sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  cases b <;> norm_num [sign]

/-- Flip precisely one coordinate in a Boolean assignment. -/
def flip (i : κ) : (κ → Bool) ≃ (κ → Bool) where
  toFun σ := Function.update σ i (!(σ i))
  invFun σ := Function.update σ i (!(σ i))
  left_inv σ := by
    funext j
    by_cases hj : j = i <;> simp [hj, Function.update]
  right_inv σ := by
    funext j
    by_cases hj : j = i <;> simp [hj, Function.update]

/-- Orthogonality of the independent signs under the exact finite sum. -/
lemma sum_sign_mul (i j : κ) :
    ∑ σ : κ → Bool, sign (σ i) * sign (σ j) =
      if i = j then (Fintype.card (κ → Bool) : ℝ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp [sign_mul_self]
  · rw [if_neg hij]
    have he : (∑ σ : κ → Bool, sign (σ i) * sign (σ j)) =
        -(∑ σ : κ → Bool, sign (σ i) * sign (σ j)) := by
      calc
        _ = ∑ σ : κ → Bool, sign (flip i σ i) * sign (flip i σ j) :=
          (Equiv.sum_comp (flip i) _).symm
        _ = -(∑ σ : κ → Bool, sign (σ i) * sign (σ j)) := by
          simp [flip, Function.update, Ne.symm hij, sign_not,
            Finset.sum_neg_distrib]
    linarith

/-- The sum of squares of all signed combinations has no mixed terms. -/
lemma matrix_signed_second_moment (B : κ → Matrix d d ℂ) :
    (∑ σ : κ → Bool, (∑ i, sign (σ i) • B i) ^ 2) =
      (Fintype.card (κ → Bool) : ℝ) • (∑ i, B i ^ 2) := by
  calc
    _ = ∑ i, ∑ j, (∑ σ : κ → Bool, sign (σ i) * sign (σ j)) •
        (B i * B j) := by
      simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        Algebra.mul_smul_comm, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = _ := by
      simp [sum_sign_mul, Finset.smul_sum, pow_two]

/-- The Hermitian signed combination of a finite family. -/
def signedSum (B : κ → HermitianMat d ℂ) (σ : κ → Bool) : HermitianMat d ℂ :=
  ∑ i, sign (σ i) • B i

/-- Exact second moment, stated in the Hermitian-matrix space. -/
lemma signed_second_moment (B : κ → HermitianMat d ℂ) :
    (∑ σ : κ → Bool, signedSum B σ ^ 2) =
      (Fintype.card (κ → Bool) : ℝ) • (∑ i, B i ^ 2) := by
  apply HermitianMat.ext
  simpa only [signedSum, HermitianMat.mat_finset_sum, HermitianMat.mat_pow,
    HermitianMat.mat_smul] using matrix_signed_second_moment (fun i => (B i).mat)

/-- All signed combinations of a quadratically isotropic family force a
uniform lower bound on their summed even powers. -/
lemma signed_even_moment_lower (B : κ → HermitianMat d ℂ) (a : ℝ)
    (ha : 0 ≤ a) (L : ℕ) (hB : ∑ i, B i ^ 2 = a • 1) :
    ((Fintype.card (κ → Bool) : ℝ) * a ^ L) • (1 : HermitianMat d ℂ) ≤
      ∑ σ : κ → Bool, signedSum B σ ^ (2 * L) := by
  apply even_moment_lower (signedSum B) a ha L
  rw [signed_second_moment, hB, smul_smul]

end Signs

section Quadratures
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The Hermitian real quadrature of a matrix. -/
def realQuadrature (V : Matrix d d ℂ) : HermitianMat d ℂ :=
  ⟨V + V.conjTranspose, Matrix.isHermitian_add_transpose_self V⟩

/-- The Hermitian imaginary quadrature of a matrix. -/
def imagQuadrature (V : Matrix d d ℂ) : HermitianMat d ℂ :=
  ⟨Complex.I • (V - V.conjTranspose), by
    change (Complex.I • (V - V.conjTranspose)).conjTranspose = _
    rw [Matrix.conjTranspose_smul]
    simp only [Complex.star_def, Complex.conj_I, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, neg_smul]
    rw [← smul_neg, neg_sub]⟩

/-- For a unitary matrix the sum of its two quadrature squares is exactly four. -/
lemma quadrature_square_sum (V : Matrix d d ℂ)
    (hV : V * V.conjTranspose = 1) (hV' : V.conjTranspose * V = 1) :
    realQuadrature V ^ 2 + imagQuadrature V ^ 2 =
      (4 : ℝ) • (1 : HermitianMat d ℂ) := by
  apply HermitianMat.ext
  change (V + V.conjTranspose) ^ 2 + (Complex.I • (V - V.conjTranspose)) ^ 2 =
    (4 : ℝ) • (1 : Matrix d d ℂ)
  simp only [pow_two, smul_mul_assoc,
    Algebra.mul_smul_comm, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  calc
    _ = 2 • (V * V.conjTranspose) + 2 • (V.conjTranspose * V) := by
      noncomm_ring
    _ = _ := by
      rw [hV, hV']
      rw [← add_smul]
      exact (Nat.cast_smul_eq_nsmul ℝ 4 (1 : Matrix d d ℂ)).symm

/-- Both quadratures for every member of a finite matrix family. -/
def quadratureFamily (V : κ → Matrix d d ℂ) (e : κ × Bool) : HermitianMat d ℂ :=
  if e.2 then imagQuadrature (V e.1) else realQuadrature (V e.1)

omit [DecidableEq κ] in
/-- The quadrature family of unitaries is exactly quadratically isotropic. -/
lemma quadrature_family_second_moment (V : κ → Matrix d d ℂ)
    (hV : ∀ i, V i * (V i).conjTranspose = 1)
    (hV' : ∀ i, (V i).conjTranspose * V i = 1) :
    (∑ e : κ × Bool, quadratureFamily V e ^ 2) =
      (4 * (Fintype.card κ : ℝ)) • (1 : HermitianMat d ℂ) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, quadratureFamily, Bool.false_eq_true, ↓reduceIte]
  simp_rw [add_comm (imagQuadrature _ ^ 2), quadrature_square_sum _ (hV _) (hV' _)]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, mul_comm]

/-- The full Gaussian-sign matrix subfamily forces an actual uniform spectral
lower bound on its even-power sum, using only the unitarity hypotheses. -/
lemma unitary_gaussian_sign_lower (V : κ → Matrix d d ℂ)
    (hV : ∀ i, V i * (V i).conjTranspose = 1)
    (hV' : ∀ i, (V i).conjTranspose * V i = 1) (L : ℕ) :
    ((2 : ℝ) ^ (2 * Fintype.card κ) * (4 * (Fintype.card κ : ℝ)) ^ L) •
        (1 : HermitianMat d ℂ) ≤
      ∑ σ : (κ × Bool) → Bool, signedSum (quadratureFamily V) σ ^ (2 * L) := by
  have h := signed_even_moment_lower (quadratureFamily V)
    (4 * (Fintype.card κ : ℝ)) (by positivity) L
    (quadrature_family_second_moment V hV hV')
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod,
    Nat.cast_pow, Nat.cast_ofNat, mul_comm (Fintype.card κ) 2] using h

end Quadratures

section FullFilter
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Real scalar multiplication commutes with Hermitian matrix powers. -/
lemma real_smul_pow (t : ℝ) (Z : HermitianMat d ℂ) (L : ℕ) :
    (t • Z) ^ L = t ^ L • Z ^ L := by
  apply HermitianMat.ext
  simpa only [HermitianMat.mat_smul, HermitianMat.mat_pow] using
    smul_pow t Z.mat L

/-- The same Gaussian-sign bound after the filter's scalar normalization. -/
lemma normalized_unitary_gaussian_sign_lower (V : κ → Matrix d d ℂ)
    (hV : ∀ i, V i * (V i).conjTranspose = 1)
    (hV' : ∀ i, (V i).conjTranspose * V i = 1) (t : ℝ) (L : ℕ) :
    ((2 : ℝ) ^ (2 * Fintype.card κ) *
        (4 * (Fintype.card κ : ℝ) * t ^ 2) ^ L) • (1 : HermitianMat d ℂ) ≤
      ∑ σ : (κ × Bool) → Bool, (t • signedSum (quadratureFamily V) σ) ^ (2 * L) := by
  have ht := smul_le_smul_of_nonneg_left (unitary_gaussian_sign_lower V hV hV' L)
    (FiniteFilterSupport.scalar_even_nonneg t L)
  rw [smul_smul] at ht
  simp_rw [real_smul_pow, ← Finset.smul_sum]
  have heq : (2 : ℝ) ^ (2 * Fintype.card κ) *
      (4 * (Fintype.card κ : ℝ) * t ^ 2) ^ L =
      t ^ (2 * L) *
        (2 ^ (2 * Fintype.card κ) * (4 * (Fintype.card κ : ℝ)) ^ L) := by
    rw [mul_pow, ← pow_mul]
    ring
  rw [heq]
  exact ht

/-- A subfamily's nonnegative even powers are bounded by the full finite filter. -/
lemma embedded_even_sum_le_filter (Z : ι → HermitianMat d ℂ)
    {η : Type*} [Fintype η] (e : η ↪ ι) (L : ℕ) :
    (∑ j, Z (e j) ^ (2 * L)) ≤ FiniteFilterSupport.filter Z L := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.image e, Z i ^ (2 * L) := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact e.injective hab
    _ ≤ ∑ i, Z i ^ (2 * L) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact FiniteFilterSupport.even_power_nonneg (Z i) L
    _ = _ := rfl

/-- If the finite filter contains the full Gaussian-sign family, its actual
matrix sum satisfies the normalized Gaussian-sign lower bound.  The embedding
is explicit data; no lower bound on the filter is assumed. -/
lemma full_filter_gaussian_sign_lower (Z : ι → HermitianMat d ℂ)
    (V : κ → Matrix d d ℂ)
    (hV : ∀ i, V i * (V i).conjTranspose = 1)
    (hV' : ∀ i, (V i).conjTranspose * V i = 1)
    (e : ((κ × Bool) → Bool) ↪ ι) (t : ℝ) (L : ℕ)
    (hZ : ∀ σ, Z (e σ) = t • signedSum (quadratureFamily V) σ) :
    ((2 : ℝ) ^ (2 * Fintype.card κ) *
        (4 * (Fintype.card κ : ℝ) * t ^ 2) ^ L) • (1 : HermitianMat d ℂ) ≤
      FiniteFilterSupport.filter Z L := by
  calc
    _ ≤ ∑ σ : (κ × Bool) → Bool,
        (t • signedSum (quadratureFamily V) σ) ^ (2 * L) :=
      normalized_unitary_gaussian_sign_lower V hV hV' t L
    _ = ∑ σ, Z (e σ) ^ (2 * L) := by simp only [hZ]
    _ ≤ _ := embedded_even_sum_le_filter Z e L

end FullFilter

#print axioms even_power_supporting_line
#print axioms even_moment_lower
#print axioms matrix_signed_second_moment
#print axioms signed_even_moment_lower
#print axioms quadrature_square_sum
#print axioms unitary_gaussian_sign_lower
#print axioms normalized_unitary_gaussian_sign_lower
#print axioms full_filter_gaussian_sign_lower

end SignFilterLower
