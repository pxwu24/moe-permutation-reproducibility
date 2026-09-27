import GridCardinality
import SignFilterLower

/-! # A. The full Gaussian sign family inside the integer matrix grid

Independent signs are assigned to the real and imaginary parts of every
strict upper-triangular entry. The resulting matrices are distinct members
of the actual filter grid for every `C₁ > 2` and `k ≥ 2`.
-/

noncomputable section
open scoped BigOperators

namespace GaussianSignGrid

variable {k : ℕ}

/-- Strict upper-triangular positions. -/
def UpperEdge (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

instance : Fintype (UpperEdge k) := inferInstanceAs
  (Fintype {p : Fin k × Fin k // p.1 < p.2})

/-- Two independent signs produce one Gaussian integer `±1 ± i`. -/
def signedEntry (σ : (UpperEdge k × Bool) → Bool) (e : UpperEdge k) : ℂ :=
  (SignFilterLower.sign (σ (e,false)) : ℂ) +
    (SignFilterLower.sign (σ (e,true)) : ℂ) * Complex.I

/-- Gaussian sign matrix: use the prescribed upper entries and their
conjugates below the diagonal. -/
def signedMatrix (σ : (UpperEdge k × Bool) → Bool) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => if h : i < j then signedEntry σ ⟨(i,j),h⟩
    else if h' : j < i then star (signedEntry σ ⟨(j,i),h'⟩) else 0

lemma signedMatrix_isHermitian (σ : (UpperEdge k × Bool) → Bool) :
    (signedMatrix σ).IsHermitian := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [Matrix.conjTranspose_apply, signedMatrix, hij, not_lt_of_gt hij]
  · subst j; simp [Matrix.conjTranspose_apply, signedMatrix]
  · simp [Matrix.conjTranspose_apply, signedMatrix, hij, not_lt_of_gt hij]

/-- The Gaussian sign matrix packaged as a Hermitian matrix. -/
def signedHermitian (σ : (UpperEdge k × Bool) → Bool) : HermitianMat (Fin k) ℂ :=
  ⟨signedMatrix σ, signedMatrix_isHermitian σ⟩

lemma signedHermitian_diag (σ : (UpperEdge k × Bool) → Bool) (i : Fin k) :
    signedHermitian σ i i = 0 := by
  change signedMatrix σ i i = 0
  simp [signedMatrix]

lemma signedHermitian_upper (σ : (UpperEdge k × Bool) → Bool)
    (i j : Fin k) (hij : i < j) :
    signedHermitian σ i j = signedEntry σ ⟨(i,j),hij⟩ := by
  change signedMatrix σ i j = _
  simp [signedMatrix, hij]

lemma signedEntry_gaussian (σ : (UpperEdge k × Bool) → Bool) (e : UpperEdge k) :
    ∃ p q : ℤ, signedEntry σ e = (p : ℂ) + (q : ℂ) * Complex.I := by
  cases h₁ : σ (e,false) <;> cases h₂ : σ (e,true)
  · exact ⟨-1,-1, by simp [signedEntry, h₁, h₂, SignFilterLower.sign]⟩
  · exact ⟨-1,1, by simp [signedEntry, h₁, h₂, SignFilterLower.sign]⟩
  · exact ⟨1,-1, by simp [signedEntry, h₁, h₂, SignFilterLower.sign]⟩
  · exact ⟨1,1, by simp [signedEntry, h₁, h₂, SignFilterLower.sign]⟩

lemma signedHermitian_gaussian (σ : (UpperEdge k × Bool) → Bool) (i j : Fin k) :
    ∃ p q : ℤ, signedHermitian σ i j = (p : ℂ) + (q : ℂ) * Complex.I := by
  change ∃ p q : ℤ, signedMatrix σ i j = (p : ℂ) + (q : ℂ) * Complex.I
  rcases lt_trichotomy i j with hij | hij | hij
  · simpa [signedMatrix, hij] using signedEntry_gaussian σ ⟨(i,j),hij⟩
  · subst j; exact ⟨0,0,by simp [signedMatrix]⟩
  · obtain ⟨p,q,hpq⟩ := signedEntry_gaussian σ ⟨(j,i),hij⟩
    refine ⟨p,-q,?_⟩
    simp [signedMatrix, hij, not_lt_of_gt hij, hpq]

lemma signedEntry_energy (σ : (UpperEdge k × Bool) → Bool) (e : UpperEdge k) :
    ‖signedEntry σ e‖ ^ 2 = 2 := by
  cases h₁ : σ (e,false) <;> cases h₂ : σ (e,true) <;>
    norm_num [signedEntry, h₁, h₂, SignFilterLower.sign, Complex.sq_norm,
      Complex.normSq_apply]

lemma signedHermitian_entry_energy (σ : (UpperEdge k × Bool) → Bool)
    (i j : Fin k) : ‖signedHermitian σ i j‖ ^ 2 = if i = j then 0 else 2 := by
  change ‖signedMatrix σ i j‖ ^ 2 = _
  rcases lt_trichotomy i j with hij | hij | hij
  · simp only [signedMatrix, dif_pos hij, if_neg (ne_of_lt hij)]
    exact signedEntry_energy σ _
  · subst j; simp [signedMatrix]
  · simp only [signedMatrix, dif_neg (not_lt_of_gt hij), dif_pos hij,
      norm_star, if_neg (ne_of_gt hij)]
    exact signedEntry_energy σ _

/-- Every off-diagonal entry has squared modulus two. -/
lemma signedHermitian_norm_sq (σ : (UpperEdge k × Bool) → Bool) :
    ‖signedHermitian σ‖ ^ 2 = 2 * ((k : ℝ)^2 - k) := by
  rw [GaussianHermitianGrid.norm_sq_entries, Fintype.sum_prod_type]
  simp_rw [signedHermitian_entry_energy]
  have he : ∀ i j : Fin k, (if i = j then (0 : ℝ) else 2) =
      2 - (if i = j then 2 else 0) := by
    intro i j; split <;> norm_num
  simp_rw [he]
  simp [Finset.sum_sub_distrib]
  ring

/-- Every Gaussian sign matrix belongs to the exact integer grid when
`C₁ > 2` and `k ≥ 2`. -/
lemma signedHermitian_inGrid (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (σ : (UpperEdge k × Bool) → Bool) :
    GaussianHermitianGrid.InGrid C₁ (signedHermitian σ) := by
  refine ⟨signedHermitian_diag σ, signedHermitian_gaussian σ, ?_, ?_⟩
  · rw [signedHermitian_norm_sq]
    have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  · rw [signedHermitian_norm_sq]
    have hkr : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg (show 0 ≤ C₁-2 by linarith) (sq_nonneg (k : ℝ))]

lemma sign_injective : Function.Injective SignFilterLower.sign := by
  intro a b h
  cases a <;> cases b <;> norm_num [SignFilterLower.sign] at *

/-- All sign assignments give distinct matrices. -/
lemma signedHermitian_injective : Function.Injective
    (signedHermitian (k := k)) := by
  intro σ τ h
  funext p
  obtain ⟨e,b⟩ := p
  have he := congrArg (fun W : HermitianMat (Fin k) ℂ => W e.val.1 e.val.2) h
  rw [signedHermitian_upper σ _ _ e.property,
    signedHermitian_upper τ _ _ e.property] at he
  have hee : (⟨(e.val.1,e.val.2),e.property⟩ : UpperEdge k) = e := by
    apply Subtype.ext
    exact Prod.mk.eta
  rw [hee] at he
  cases b
  · apply sign_injective
    simpa only [signedEntry, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero] using congrArg Complex.re he
  · apply sign_injective
    simpa only [signedEntry, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      zero_add, add_zero] using congrArg Complex.im he

/-- Explicit injection of every Gaussian sign assignment into the actual
filter-index subtype. -/
def gridEmbedding (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k) :
    ((UpperEdge k × Bool) → Bool) ↪
      {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W} where
  toFun σ := ⟨signedHermitian σ, signedHermitian_inGrid C₁ hC₁ hk σ⟩
  inj' := fun _ _ h => signedHermitian_injective (congrArg Subtype.val h)

lemma upperEdge_card : Fintype.card (UpperEdge k) = k.choose 2 := by
  classical
  change Fintype.card {p : Fin k × Fin k // p.1 < p.2} = k.choose 2
  rw [Fintype.card_subtype]
  have h := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin k)))
  simpa only [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] using h

lemma twice_upperEdge_card : 2 * Fintype.card (UpperEdge k) = k * (k - 1) := by
  rw [upperEdge_card]
  have h := Nat.descFactorial_eq_factorial_mul_choose k 2
  simpa [Nat.mul_comm] using h.symm

#print axioms signedHermitian_inGrid
#print axioms signedHermitian_injective
#print axioms twice_upperEdge_card

end GaussianSignGrid
