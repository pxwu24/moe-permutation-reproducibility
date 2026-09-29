import QuantumInfo.ForMathlib.HermitianMat.Sqrt
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Normed.Operator.Basic

/-! Finite spectral filters: an actual noncommutative matrix contraction theorem,
followed by a general real-linear net-extension theorem. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open ComplexOrder

namespace FiniteFilterSupport

lemma scalar_even_nonneg (x : ℝ) (L : ℕ) : 0 ≤ x ^ (2 * L) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg x) L

lemma abs_le_one_add_even_pow (x : ℝ) (L : ℕ) (hL : 1 ≤ L) :
    |x| ≤ 1 + x ^ (2 * L) := by
  have he : |x| ^ (2 * L) = x ^ (2 * L) := by
    rw [← abs_pow, abs_of_nonneg (scalar_even_nonneg x L)]
  by_cases hx : |x| ≤ 1
  · linarith [scalar_even_nonneg x L]
  · have hh := le_self_pow₀ (le_of_lt (lt_of_not_ge hx))
        (show 2 * L ≠ 0 by omega)
    rw [he] at hh
    linarith

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

lemma even_power_nonneg (Z : HermitianMat d ℂ) (L : ℕ) : 0 ≤ Z ^ (2 * L) := by
  rw [← HermitianMat.cfc_pow, HermitianMat.cfc_nonneg_iff]
  intro i
  exact scalar_even_nonneg _ _

lemma le_one_add_even_power (Z : HermitianMat d ℂ) (L : ℕ) (hL : 1 ≤ L) :
    Z ≤ 1 + Z ^ (2 * L) := by
  rw [← sub_nonneg]
  have hp : 0 ≤ Z.cfc (fun x => 1 + x ^ (2 * L) - x) := by
    rw [HermitianMat.cfc_nonneg_iff]
    intro i
    have hh := abs_le_one_add_even_pow (Z.H.eigenvalues i) L hL
    have ha := le_abs_self (Z.H.eigenvalues i)
    linarith
  simpa only [HermitianMat.cfc_sub_apply, HermitianMat.cfc_add_apply,
    HermitianMat.cfc_const, one_smul, HermitianMat.cfc_pow, HermitianMat.cfc_id'] using hp

lemma neg_le_one_add_even_power (Z : HermitianMat d ℂ) (L : ℕ) (hL : 1 ≤ L) :
    -Z ≤ 1 + Z ^ (2 * L) := by
  rw [← sub_nonneg]
  have hp : 0 ≤ Z.cfc (fun x => 1 + x ^ (2 * L) - (-x)) := by
    rw [HermitianMat.cfc_nonneg_iff]
    intro i
    have hh := abs_le_one_add_even_pow (Z.H.eigenvalues i) L hL
    have ha := neg_le_abs (Z.H.eigenvalues i)
    linarith
  have hn : Z.cfc (fun x => -x) = -Z := by
    simpa only [HermitianMat.cfc_id'] using
      (HermitianMat.cfc_neg_apply Z (fun x => x))
  simpa only [HermitianMat.cfc_sub_apply, HermitianMat.cfc_add_apply,
    HermitianMat.cfc_const, one_smul, HermitianMat.cfc_pow,
    hn] using hp

def filter (Z : ι → HermitianMat d ℂ) (L : ℕ) : HermitianMat d ℂ :=
  ∑ i, Z i ^ (2 * L)

def damping (Z : ι → HermitianMat d ℂ) (L : ℕ) : HermitianMat d ℂ :=
  (1 + filter Z L)⁻¹.sqrt

lemma filter_nonneg (Z : ι → HermitianMat d ℂ) (L : ℕ) : 0 ≤ filter Z L := by
  exact Finset.sum_nonneg fun i _ => even_power_nonneg (Z i) L

lemma summand_le_filter (Z : ι → HermitianMat d ℂ) (L : ℕ) (i : ι) :
    Z i ^ (2 * L) ≤ filter Z L := by
  exact Finset.single_le_sum (fun j _ => even_power_nonneg (Z j) L) (Finset.mem_univ i)

lemma damping_identity (Z : ι → HermitianMat d ℂ) (L : ℕ) :
    (1 + filter Z L).conj (damping Z L).mat = 1 := by
  have hp : (1 + filter Z L).mat.PosDef := by
    simpa using Matrix.PosDef.one.add_posSemidef
      (HermitianMat.zero_le_iff.mp (filter_nonneg Z L))
  apply HermitianMat.ext
  simpa only [HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat,
    HermitianMat.mat_one, damping] using HermitianMat.sqrt_inv_mul_self_mul_sqrt_inv_eq_one hp

theorem filter_contraction_order (Z : ι → HermitianMat d ℂ) (L : ℕ)
    (hL : 1 ≤ L) (i : ι) :
    -(1 : HermitianMat d ℂ) ≤ (Z i).conj (damping Z L).mat ∧
    (Z i).conj (damping Z L).mat ≤ 1 := by
  have hplus : Z i ≤ 1 + filter Z L :=
    (le_one_add_even_power (Z i) L hL).trans
      (add_le_add le_rfl (summand_le_filter Z L i))
  have hminus : -Z i ≤ 1 + filter Z L :=
    (neg_le_one_add_even_power (Z i) L hL).trans
      (add_le_add le_rfl (summand_le_filter Z L i))
  have hp := HermitianMat.conj_mono (M := (damping Z L).mat) hplus
  have hm := HermitianMat.conj_mono (M := (damping Z L).mat) hminus
  rw [damping_identity] at hp hm
  rw [map_neg] at hm
  exact ⟨by simpa only [neg_neg] using neg_le_neg hm, hp⟩

open MatrixOrder in
lemma operator_norm_le_one_of_order (B : HermitianMat d ℂ)
    (hlo : -(1 : HermitianMat d ℂ) ≤ B) (hhi : B ≤ 1) : ‖B.mat‖ ≤ 1 := by
  have hh : B.mat ≤ algebraMap ℝ (Matrix d d ℂ) 1 := by
    change B.mat ≤ 1 at hhi
    simpa using hhi
  have hl : algebraMap ℝ (Matrix d d ℂ) (-1) ≤ B.mat := by
    change -(1 : Matrix d d ℂ) ≤ B.mat at hlo
    simpa using hlo
  have hs := (le_algebraMap_iff_spectrum_le B.isSelfAdjoint).mp hh
  have ht := (algebraMap_le_iff_le_spectrum B.isSelfAdjoint).mp hl
  have hnorm : ‖cfc (fun x : ℝ => x) B.mat‖ ≤ 1 := by
    apply norm_cfc_le zero_le_one
    intro x hx
    exact (Real.norm_eq_abs x).symm ▸ (abs_le.mpr ⟨ht x hx, hs x hx⟩)
  rw [cfc_id' ℝ B.mat B.isSelfAdjoint] at hnorm
  exact hnorm

theorem filter_contraction_norm (Z : ι → HermitianMat d ℂ) (L : ℕ)
    (hL : 1 ≤ L) (i : ι) :
    ‖(damping Z L).mat * (Z i).mat * (damping Z L).mat‖ ≤ 1 := by
  have ho := filter_contraction_order Z L hL i
  have hn := operator_norm_le_one_of_order _ ho.1 ho.2
  simpa only [HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat] using hn

section Net
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A norm bound on a δ-net extends to the whole space with loss (1-δ)⁻¹.
The approximating points need not themselves lie on the unit sphere. -/
theorem norm_le_of_net (T : E →L[ℝ] V) (S : Set E) (δ B : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ S, ‖x - y‖ ≤ δ)
    (hbound : ∀ y ∈ S, ‖T y‖ ≤ B) : ‖T‖ ≤ B / (1 - δ) := by
  have hpre : ‖T‖ ≤ B + ‖T‖ * δ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm
    · positivity
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    calc
      ‖T x‖ = ‖T y + T (x-y)‖ := by rw [← map_add]; congr 1; abel_nf
      _ ≤ ‖T y‖ + ‖T (x-y)‖ := norm_add_le _ _
      _ ≤ B + ‖T‖ * δ := add_le_add (hbound y hy)
        ((T.le_opNorm (x-y)).trans (mul_le_mul_of_nonneg_left hxy (norm_nonneg T)))
  apply (le_div_iff₀ (sub_pos.mpr hδ1)).mpr
  nlinarith

theorem apply_norm_le_of_net (T : E →L[ℝ] V) (S : Set E) (δ B : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hB : 0 ≤ B)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ S, ‖x - y‖ ≤ δ)
    (hbound : ∀ y ∈ S, ‖T y‖ ≤ B) (x : E) :
    ‖T x‖ ≤ B / (1 - δ) * ‖x‖ := by
  exact (T.le_opNorm x).trans (mul_le_mul_of_nonneg_right
    (norm_le_of_net T S δ B hδ hδ1 hB hnet hbound) (norm_nonneg x))
end Net

section MatrixNet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def compressedMap (A : E →L[ℝ] Matrix d d ℂ) (H : Matrix d d ℂ) :
    E →L[ℝ] Matrix d d ℂ where
  toFun x := H * A x * H
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' t x := by simp [Algebra.mul_smul_comm]
  cont := (continuous_const.mul A.continuous).mul continuous_const

lemma scaled_contraction (Z : ι → HermitianMat d ℂ) (L : ℕ)
    (hL : 1 ≤ L) (i : ι) (a γ : ℝ) (ha : 0 ≤ a) (hγ : 0 ≤ γ) :
    ‖(Real.sqrt γ • (damping Z L).mat) * (a • (Z i).mat) *
      (Real.sqrt γ • (damping Z L).mat)‖ ≤ γ * a := by
  have heq : (Real.sqrt γ • (damping Z L).mat) * (a • (Z i).mat) *
      (Real.sqrt γ • (damping Z L).mat) =
      (γ * a) • ((damping Z L).mat * (Z i).mat * (damping Z L).mat) := by
    simp only [Algebra.mul_smul_comm, smul_mul_assoc, smul_smul]
    congr 1
    nlinarith [Real.mul_self_sqrt hγ]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hγ ha)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (filter_contraction_norm Z L hL i) (mul_nonneg hγ ha)

/-- The full finite-filter/net argument for an actual matrix-valued real-linear map.
Here `A (y i) = a • Z i` records the chosen normalization of the finite tests.
The only geometric premise is the stated δ-net property; no filtered norm bound
is assumed. -/
theorem finite_filter_net_bound (A : E →L[ℝ] Matrix d d ℂ)
    (y : ι → E) (Z : ι → HermitianMat d ℂ) (L : ℕ) (hL : 1 ≤ L)
    (a γ δ : ℝ) (ha : 0 ≤ a) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hA : ∀ i, A (y i) = a • (Z i).mat)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ i, ‖x - y i‖ ≤ δ) (x : E) :
    ‖(Real.sqrt γ • (damping Z L).mat) * A x *
      (Real.sqrt γ • (damping Z L).mat)‖ ≤ γ * a / (1 - δ) * ‖x‖ := by
  let H : Matrix d d ℂ := Real.sqrt γ • (damping Z L).mat
  let T := compressedMap A H
  have hn : ∀ u : E, ‖u‖ = 1 → ∃ v ∈ Set.range y, ‖u-v‖ ≤ δ := by
    intro u hu
    obtain ⟨i, hi⟩ := hnet u hu
    exact ⟨y i, ⟨i, rfl⟩, hi⟩
  have hb : ∀ v ∈ Set.range y, ‖T v‖ ≤ γ * a := by
    rintro _ ⟨i, rfl⟩
    change ‖H * A (y i) * H‖ ≤ γ * a
    rw [hA i]
    exact scaled_contraction Z L hL i a γ ha hγ
  exact apply_norm_le_of_net T (Set.range y) δ (γ*a) hδ hδ1
    (mul_nonneg hγ ha) hn hb x
end MatrixNet

#print axioms filter_contraction_order
#print axioms filter_contraction_norm
#print axioms norm_le_of_net
#print axioms apply_norm_le_of_net
#print axioms finite_filter_net_bound

end FiniteFilterSupport
