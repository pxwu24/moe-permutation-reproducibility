import GridNet
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-! # A. Cardinality of the Gaussian Hermitian filter grid

This standalone verification module counts the actual matrix grid from
`GridNet`, without assuming a bound on its size.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace GaussianHermitianGrid

variable {k : ℕ}

/-- The squared Hilbert--Schmidt norm is the sum of all entry energies. -/
lemma norm_sq_entries (W : HermitianMat (Fin k) ℂ) :
    ‖W‖ ^ 2 = ∑ p : Fin k × Fin k, ‖W p.1 p.2‖ ^ 2 := by
  rw [HermitianMat.norm_eq_frobenius, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (by positivity)]
  simp only [Fintype.sum_prod_type]

/-- Each off-diagonal entry contributes twice to the squared matrix norm. -/
lemma twice_entry_energy_le (W : HermitianMat (Fin k) ℂ) (i j : Fin k)
    (hij : i ≠ j) : 2 * ‖W i j‖ ^ 2 ≤ ‖W‖ ^ 2 := by
  classical
  have hne : (i,j) ≠ (j,i) := by intro h; exact hij (Prod.mk.inj h).1
  have he : ‖W j i‖ = ‖W i j‖ := by
    have hh : W j i = star (W i j) := (congrFun (congrFun W.H j) i).symm
    rw [hh, norm_star]
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({(i,j),(j,i)} : Finset (Fin k × Fin k)) ⊆ Finset.univ from
      Finset.subset_univ _)
    (fun p _ _ => sq_nonneg ‖W p.1 p.2‖)
  rw [Finset.sum_pair hne, ← norm_sq_entries W, he] at hs
  linarith

/-- The real and imaginary coordinates are strictly inside the radius
`sqrt C₁ * k`; strictness removes both integer endpoints when necessary. -/
lemma grid_entry_coordinate_lt (C₁ : ℝ) (hC₁ : 0 < C₁) (hk : 0 < k)
    (W : HermitianMat (Fin k) ℂ) (hW : InGrid C₁ W)
    (i j : Fin k) (hij : i ≠ j) :
    |(W i j).re| < Real.sqrt C₁ * (k : ℝ) ∧
    |(W i j).im| < Real.sqrt C₁ * (k : ℝ) := by
  have he := twice_entry_energy_le W i j hij
  have hb : 0 < Real.sqrt C₁ * (k : ℝ) := by positivity
  have hb2 : (Real.sqrt C₁ * (k : ℝ)) ^ 2 = C₁ * (k : ℝ)^2 := by
    rw [mul_pow, Real.sq_sqrt hC₁.le]
  have he2 : ‖W i j‖ ^ 2 = (W i j).re ^ 2 + (W i j).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  constructor
  · have hs : |(W i j).re| ^ 2 < (Real.sqrt C₁ * (k : ℝ)) ^ 2 := by
      rw [sq_abs, hb2]
      nlinarith [hW.2.2.2, sq_nonneg (W i j).re, sq_nonneg (W i j).im]
    exact (sq_lt_sq₀ (abs_nonneg _) hb.le).mp hs
  · have hs : |(W i j).im| ^ 2 < (Real.sqrt C₁ * (k : ℝ)) ^ 2 := by
      rw [sq_abs, hb2]
      nlinarith [hW.2.2.2, sq_nonneg (W i j).re, sq_nonneg (W i j).im]
    exact (sq_lt_sq₀ (abs_nonneg _) hb.le).mp hs

/-- Directed off-diagonal pairs index the independent real coordinates:
upper pairs store real parts and reversed pairs store imaginary parts. -/
def GridCoordinate (k : ℕ) := ↥((Finset.univ : Finset (Fin k)).offDiag)

instance : Fintype (GridCoordinate k) := inferInstanceAs
  (Fintype ↥((Finset.univ : Finset (Fin k)).offDiag))

lemma gridCoordinate_card : Fintype.card (GridCoordinate k) = k * (k - 1) := by
  classical
  change Fintype.card ↥((Finset.univ : Finset (Fin k)).offDiag) = k * (k - 1)
  rw [Fintype.card_coe]
  simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]

/-- One independent real coordinate of a Hermitian matrix. -/
def realCoordinate (W : HermitianMat (Fin k) ℂ) (p : GridCoordinate k) : ℝ :=
  if p.val.1 < p.val.2 then (W p.val.1 p.val.2).re
  else (W p.val.2 p.val.1).im

lemma realCoordinate_integer (C₁ : ℝ) (W : HermitianMat (Fin k) ℂ)
    (hW : InGrid C₁ W) (p : GridCoordinate k) :
    ∃ z : ℤ, realCoordinate W p = (z : ℝ) := by
  unfold realCoordinate
  split
  · obtain ⟨a,b,hab⟩ := hW.2.1 p.val.1 p.val.2
    exact ⟨a, by simp [hab]⟩
  · obtain ⟨a,b,hab⟩ := hW.2.1 p.val.2 p.val.1
    exact ⟨b, by simp [hab]⟩

lemma realCoordinate_lt (C₁ : ℝ) (hC₁ : 0 < C₁) (hk : 0 < k)
    (W : HermitianMat (Fin k) ℂ) (hW : InGrid C₁ W)
    (p : GridCoordinate k) : |realCoordinate W p| < Real.sqrt C₁ * (k : ℝ) := by
  have hp : p.val.1 ≠ p.val.2 := (Finset.mem_offDiag.mp p.property).2.2
  unfold realCoordinate
  split
  · exact (grid_entry_coordinate_lt C₁ hC₁ hk W hW _ _ hp).1
  · exact (grid_entry_coordinate_lt C₁ hC₁ hk W hW _ _ hp.symm).2

/-- Independent coordinates determine every zero-diagonal Hermitian matrix. -/
lemma realCoordinate_injective (W V : HermitianMat (Fin k) ℂ)
    (hW : ∀ i, W i i = 0) (hV : ∀ i, V i i = 0)
    (h : realCoordinate W = realCoordinate V) : W = V := by
  have hu : ∀ i j, i < j → W i j = V i j := by
    intro i j hij
    let p : GridCoordinate k := ⟨(i,j), Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, ne_of_lt hij⟩⟩
    let q : GridCoordinate k := ⟨(j,i), Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, ne_of_gt hij⟩⟩
    have hp := congrFun h p
    have hq := congrFun h q
    apply Complex.ext
    · simpa [realCoordinate, p, hij] using hp
    · simpa [realCoordinate, q, not_lt_of_gt hij] using hq
  apply HermitianMat.ext
  ext i j
  change W i j = V i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hu i j hij
  · subst j; rw [hW, hV]
  · have hWi : W i j = star (W j i) := (congrFun (congrFun W.H i) j).symm
    have hVi : V i j = star (V j i) := (congrFun (congrFun V.H i) j).symm
    rw [hWi, hVi, hu j i hij]

/-- Integer interval used by the grid encoding. It has exactly `2N` elements. -/
def CoordinateBox (N : ℕ) := ↥(Finset.Ico (-(N : ℤ)) (N : ℤ))

instance (N : ℕ) : Fintype (CoordinateBox N) := inferInstanceAs
  (Fintype ↥(Finset.Ico (-(N : ℤ)) (N : ℤ)))

lemma coordinateBox_card (N : ℕ) : Fintype.card (CoordinateBox N) = 2 * N := by
  classical
  change Fintype.card ↥(Finset.Ico (-(N : ℤ)) (N : ℤ)) = 2 * N
  rw [Fintype.card_coe, Int.card_Ico]
  omega

/-- Encode an actual grid matrix by its bounded integer coordinates. -/
def gridEncoding (C₁ : ℝ) (hC₁ : 0 < C₁) (hk : 0 < k)
    (W : {W : HermitianMat (Fin k) ℂ // InGrid C₁ W}) :
    GridCoordinate k → CoordinateBox (Nat.ceil (Real.sqrt C₁ * (k : ℝ))) :=
  fun p => ⟨Int.floor (realCoordinate W.val p), by
    obtain ⟨z,hz⟩ := realCoordinate_integer C₁ W.val W.property p
    have hab := realCoordinate_lt C₁ hC₁ hk W.val W.property p
    have hc := Nat.le_ceil (Real.sqrt C₁ * (k : ℝ))
    rw [hz] at hab
    rw [hz, Int.floor_intCast, Finset.mem_Ico]
    constructor
    · exact_mod_cast (show -(Nat.ceil (Real.sqrt C₁ * (k : ℝ)) : ℝ) ≤ (z : ℝ) by
        linarith [(abs_lt.mp hab).1])
    · exact_mod_cast (show (z : ℝ) < (Nat.ceil (Real.sqrt C₁ * (k : ℝ)) : ℝ) by
        linarith [(abs_lt.mp hab).2])⟩

lemma gridEncoding_injective (C₁ : ℝ) (hC₁ : 0 < C₁) (hk : 0 < k) :
    Function.Injective (gridEncoding C₁ hC₁ hk) := by
  intro W V h
  apply Subtype.ext
  apply realCoordinate_injective W.val V.val W.property.1 V.property.1
  funext p
  have hp := congrArg Subtype.val (congrFun h p)
  change Int.floor (realCoordinate W.val p) = Int.floor (realCoordinate V.val p) at hp
  obtain ⟨z,hz⟩ := realCoordinate_integer C₁ W.val W.property p
  obtain ⟨t,ht⟩ := realCoordinate_integer C₁ V.val V.property p
  simpa only [hz, ht, Int.floor_intCast] using congrArg (fun x : ℤ => (x : ℝ)) hp

/-- The exact zero-diagonal Gaussian Hermitian matrix grid is finite. -/
lemma grid_finite (C₁ : ℝ) (hC₁ : 0 < C₁) (hk : 0 < k) :
    {W : HermitianMat (Fin k) ℂ | InGrid C₁ W}.Finite := by
  classical
  apply Set.finite_coe_iff.mp
  change Finite {W : HermitianMat (Fin k) ℂ // InGrid C₁ W}
  exact Finite.of_injective (gridEncoding C₁ hC₁ hk) (gridEncoding_injective C₁ hC₁ hk)

/-- Cardinality bound for the actual matrix grid. The radius depends on
`C₁`, the grid parameter, rather than on the filter parameter `C₂`. -/
lemma grid_cardinality_le (C₁ : ℝ) (hC₁ : 0 < C₁) (hk : 0 < k) :
    Nat.card {W : HermitianMat (Fin k) ℂ // InGrid C₁ W} ≤
      (2 * Nat.ceil (Real.sqrt C₁ * (k : ℝ))) ^ (k * (k - 1)) := by
  classical
  let : Fintype {W : HermitianMat (Fin k) ℂ // InGrid C₁ W} :=
    (grid_finite C₁ hC₁ hk).fintype
  have hc := Fintype.card_le_of_injective (gridEncoding C₁ hC₁ hk)
    (gridEncoding_injective C₁ hC₁ hk)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, coordinateBox_card,
    gridCoordinate_card] using hc

#print axioms grid_entry_coordinate_lt
#print axioms grid_finite
#print axioms grid_cardinality_le

end GaussianHermitianGrid
