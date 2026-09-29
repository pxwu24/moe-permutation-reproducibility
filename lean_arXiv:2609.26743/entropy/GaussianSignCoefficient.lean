import SignFilterLower

/-!
# A. Coefficient identities for Gaussian-sign test matrices

The identities in this standalone verification file connect the entrywise
Gaussian-sign matrix with the Hermitian quadrature family used for moment bounds.
-/

noncomputable section
open scoped BigOperators

namespace GaussianSignCoefficient

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [Fintype d] [DecidableEq d] in
/-- A complex coefficient and its conjugate combine into real and imaginary
Hermitian quadratures. -/
lemma complex_pair_quadratures (V : Matrix d d ℂ) (a b : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.I) • V +
        ((a : ℂ) - (b : ℂ) * Complex.I) • V.conjTranspose =
      a • (SignFilterLower.realQuadrature V).mat +
        b • (SignFilterLower.imagQuadrature V).mat := by
  change ((a : ℂ) + (b : ℂ) * Complex.I) • V +
      ((a : ℂ) - (b : ℂ) * Complex.I) • V.conjTranspose =
    a • (V + V.conjTranspose) + b • (Complex.I • (V - V.conjTranspose))
  ext i j
  change ((a : ℂ) + (b : ℂ) * Complex.I) * V i j +
      ((a : ℂ) - (b : ℂ) * Complex.I) * V.conjTranspose i j =
    (a : ℂ) * (V i j + V.conjTranspose i j) +
      (b : ℂ) * (Complex.I * (V i j - V.conjTranspose i j))
  ring

/-- Pairwise words formed from unitary matrices are unitary. -/
lemma pair_word_unitary (U V : Matrix d d ℂ)
    (hU : U.conjTranspose * U = 1) (hU' : U * U.conjTranspose = 1)
    (hV : V.conjTranspose * V = 1) (hV' : V * V.conjTranspose = 1) :
    (U.conjTranspose * V) * (U.conjTranspose * V).conjTranspose = 1 ∧
      (U.conjTranspose * V).conjTranspose * (U.conjTranspose * V) = 1 := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  constructor
  · calc
      _ = U.conjTranspose * (V * V.conjTranspose) * U := by noncomm_ring
      _ = 1 := by rw [hV', Matrix.mul_one, hU]
  · calc
      _ = V.conjTranspose * (U * U.conjTranspose) * V := by noncomm_ring
      _ = 1 := by rw [hU', Matrix.mul_one, hV]

section Triangular
variable {k : ℕ} {E : Type*} [AddCommMonoid E]

/-- Split a zero-diagonal double sum into the two strict triangles. -/
lemma sum_eq_upper_ite (f : Fin k → Fin k → E) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) =
      ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
  have he (i j : Fin k) : f i j =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j
      simp [hdiag]
    · simp [h, not_lt_of_gt h]
  calc
    _ = ∑ i, ∑ j,
        ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => he i j
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if i < j then f j i else 0) := by
      congr 1
      exact Finset.sum_comm
    _ = _ := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp

/-- The same triangular decomposition indexed by unordered upper edges. -/
lemma sum_eq_upper_edges (f : Fin k → Fin k → E) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) =
      ∑ e : {p : Fin k × Fin k // p.1 < p.2},
        (f e.val.1 e.val.2 + f e.val.2 e.val.1) := by
  rw [sum_eq_upper_ite f hdiag]
  have hh := Finset.sum_subtype
    (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2))
    (p := fun p : Fin k × Fin k => p.1 < p.2)
    (F := inferInstance) (by simp)
    (fun p => f p.1 p.2 + f p.2 p.1)
  rw [Finset.sum_filter, Fintype.sum_prod_type] at hh
  exact hh

end Triangular

section Coefficients
variable {k : ℕ}

/-- The unordered upper-edge type for a matrix with `k` indices. -/
abbrev UpperEdge (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

/-- The actual support observable before filtering. -/
def observable (U : Fin k → Matrix d d ℂ) (W : HermitianMat (Fin k) ℂ) :
    HermitianMat d ℂ :=
  ⟨∑ i, ∑ j, W i j • ((U i).conjTranspose * U j), by
    have hW (i j : Fin k) : star (W i j) = W j i := by
      exact congrFun (congrFun W.H j) i
    change (∑ i, ∑ j, W i j • ((U i).conjTranspose * U j)).conjTranspose = _
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hW]
    exact Finset.sum_comm⟩

/-- The unitary word associated with an unordered upper edge. -/
def edgeWord (U : Fin k → Matrix d d ℂ) (e : UpperEdge k) : Matrix d d ℂ :=
  (U e.val.1).conjTranspose * U e.val.2

/-- The coefficient identity connecting an actual zero-diagonal Hermitian
matrix to the signed quadratures of its unitary words. -/
lemma observable_eq_signed_quadratures (U : Fin k → Matrix d d ℂ)
    (W : HermitianMat (Fin k) ℂ) (hdiag : ∀ i, W i i = 0)
    (σ : (UpperEdge k × Bool) → Bool)
    (hupper : ∀ e : UpperEdge k, W e.val.1 e.val.2 =
      (SignFilterLower.sign (σ (e, false)) : ℂ) +
        (SignFilterLower.sign (σ (e, true)) : ℂ) * Complex.I) :
    observable U W = SignFilterLower.signedSum
      (SignFilterLower.quadratureFamily (edgeWord U)) σ := by
  apply HermitianMat.ext
  change (∑ i, ∑ j, W i j • ((U i).conjTranspose * U j)) = _
  rw [sum_eq_upper_edges _ (fun i => by rw [hdiag, zero_smul])]
  have he (e : UpperEdge k) :
      W e.val.1 e.val.2 • ((U e.val.1).conjTranspose * U e.val.2) +
      W e.val.2 e.val.1 • ((U e.val.2).conjTranspose * U e.val.1) =
      SignFilterLower.sign (σ (e, false)) •
        (SignFilterLower.realQuadrature (edgeWord U e)).mat +
      SignFilterLower.sign (σ (e, true)) •
        (SignFilterLower.imagQuadrature (edgeWord U e)).mat := by
    have hlower : W e.val.2 e.val.1 = star (W e.val.1 e.val.2) := by
      exact (congrFun (congrFun W.H e.val.2) e.val.1).symm
    rw [hlower, hupper]
    simpa only [edgeWord, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, map_add, map_mul, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I, mul_neg, ← sub_eq_add_neg] using
      complex_pair_quadratures (edgeWord U e)
        (SignFilterLower.sign (σ (e, false))) (SignFilterLower.sign (σ (e, true)))
  rw [Finset.sum_congr rfl (fun e _ => he e)]
  simp only [SignFilterLower.signedSum, SignFilterLower.quadratureFamily,
    HermitianMat.mat_finset_sum, Fintype.sum_prod_type,
    Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  exact Finset.sum_congr rfl (fun _ _ => add_comm _ _)

end Coefficients

#print axioms complex_pair_quadratures
#print axioms pair_word_unitary
#print axioms sum_eq_upper_ite
#print axioms sum_eq_upper_edges
#print axioms observable_eq_signed_quadratures

end GaussianSignCoefficient
