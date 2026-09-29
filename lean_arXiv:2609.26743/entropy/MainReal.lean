import ActualGridFilterProperties
import MainChannel

/-! # A. Reality of the full-grid channel

Transpose permutes the Gaussian grid. For real unitary matrices it also
transposes the observable, and therefore the full filter is real. Positivity
and uniqueness of the positive square root then give the same fact for H.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open ComplexOrder

namespace MainReal

variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-- Transposition of a Hermitian matrix. -/
def transpose (W : HermitianMat d ℂ) : HermitianMat d ℂ :=
  ⟨W.mat.transpose, W.H.transpose⟩

@[simp] lemma transpose_mat (W : HermitianMat d ℂ) :
    (transpose W).mat = W.mat.transpose := rfl

@[simp] lemma transpose_apply (W : HermitianMat d ℂ) (i j : d) :
    transpose W i j = W j i := rfl

@[simp] lemma transpose_transpose (W : HermitianMat d ℂ) :
    transpose (transpose W) = W := by
  apply HermitianMat.ext
  exact Matrix.transpose_transpose W.mat

lemma transpose_norm (W : HermitianMat d ℂ) : ‖transpose W‖ = ‖W‖ := by
  rw [HermitianMat.norm_eq_frobenius, HermitianMat.norm_eq_frobenius]
  congr 1
  exact Finset.sum_comm

lemma transpose_inGrid (C₁ : ℝ) (W : HermitianMat (Fin k) ℂ)
    (hW : GaussianHermitianGrid.InGrid C₁ W) :
    GaussianHermitianGrid.InGrid C₁ (transpose W) := by
  rcases hW with ⟨hd, hg, hp, hb⟩
  exact ⟨hd, fun i j => hg j i, by simpa [transpose_norm] using hp,
    by simpa [transpose_norm] using hb⟩

/-- The conjugation/transpose symmetry of the exact finite grid. -/
def gridTranspose (C₁ : ℝ) :
    {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W} ≃
      {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W} where
  toFun W := ⟨transpose W.val, transpose_inGrid C₁ W.val W.property⟩
  invFun W := ⟨transpose W.val, transpose_inGrid C₁ W.val W.property⟩
  left_inv W := by apply Subtype.ext; exact transpose_transpose W.val
  right_inv W := by apply Subtype.ext; exact transpose_transpose W.val

lemma observable_transpose (U : Fin k → Matrix d d ℂ)
    (hU : ∀ i, (U i).transpose = (U i).conjTranspose)
    (W : HermitianMat (Fin k) ℂ) :
    (GaussianSignCoefficient.observable U W).mat.transpose =
      (GaussianSignCoefficient.observable U (transpose W)).mat := by
  have ht (i : Fin k) : (U i).conjTranspose.transpose = U i := by
    rw [← hU, Matrix.transpose_transpose]
  change (∑ i, ∑ j, W i j • ((U i).conjTranspose * U j)).transpose =
    ∑ i, ∑ j, W j i • ((U i).conjTranspose * U j)
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_mul, hU, ht]
  exact Finset.sum_comm

lemma filter_transpose (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ)
    (hU : ∀ i, (U i).transpose = (U i).conjTranspose) (L : ℕ) :
    (ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L).mat.transpose =
      (ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L).mat := by
  classical
  let : Fintype {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W} :=
    (GaussianHermitianGrid.grid_finite C₁ (by linarith) (by omega)).fintype
  simp only [ActualGridFilterLower.fullGridFilter, FiniteFilterSupport.filter,
    HermitianMat.mat_finset_sum]
  simp only [Matrix.transpose_sum, HermitianMat.mat_pow, HermitianMat.mat_smul,
    Matrix.transpose_pow, Matrix.transpose_smul, observable_transpose U hU]
  exact (gridTranspose C₁).sum_comp
    (fun W => ((C₂ * (k : ℝ))⁻¹ •
      (GaussianSignCoefficient.observable U W.val).mat) ^ (2 * L))

lemma sqrt_transpose (A : HermitianMat d ℂ) (hA : 0 ≤ A)
    (hreal : A.mat.transpose = A.mat) : A.sqrt.mat.transpose = A.sqrt.mat := by
  let X := A.sqrt.mat
  have hX : 0 ≤ X := Matrix.nonneg_iff_posSemidef.mpr
    (HermitianMat.zero_le_iff.mp (HermitianMat.sqrt_nonneg A))
  have hXT : 0 ≤ X.transpose := Matrix.nonneg_iff_posSemidef.mpr
    (HermitianMat.zero_le_iff.mp (HermitianMat.sqrt_nonneg A)).transpose
  apply (CFC.sq_eq_sq_iff X.transpose X hXT hX).mp
  have hs : X ^ 2 = A.mat := by
    simpa only [X, pow_two] using HermitianMat.sqrt_sq hA
  rw [← Matrix.transpose_pow, hs, hreal]

lemma fullGridH_transpose (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ)
    (hU : ∀ i, (U i).transpose = (U i).conjTranspose) (L : ℕ) (γ : ℝ) :
    (ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ).mat.transpose =
      (ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ).mat := by
  let F := ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L
  have hp : (1 + F).mat.PosDef := by
    simpa using Matrix.PosDef.one.add_posSemidef
      (HermitianMat.zero_le_iff.mp
        (ActualGridFilterProperties.fullGridFilter_nonneg C₁ hC₁ hk C₂ U L))
  have hi : 0 ≤ (1 + F)⁻¹ := HermitianMat.zero_le_iff.mpr hp.inv.posSemidef
  have ht : ((1 + F)⁻¹).mat.transpose = ((1 + F)⁻¹).mat := by
    simp only [HermitianMat.mat_inv, HermitianMat.mat_add, HermitianMat.mat_one,
      Matrix.transpose_nonsing_inv, Matrix.transpose_add, Matrix.transpose_one]
    rw [filter_transpose C₁ hC₁ hk C₂ U hU L]
  change (Real.sqrt γ • ((1 + F)⁻¹).sqrt.mat).transpose =
    Real.sqrt γ • ((1 + F)⁻¹).sqrt.mat
  rw [Matrix.transpose_smul, sqrt_transpose _ hi ht]

/-- Entrywise complex conjugation. -/
def bar (A : Matrix d d ℂ) : Matrix d d ℂ := A.map (starRingEnd ℂ)

@[simp] lemma bar_mul (A B : Matrix d d ℂ) : bar (A * B) = bar A * bar B :=
  Matrix.map_mul

@[simp] lemma bar_add (A B : Matrix d d ℂ) : bar (A + B) = bar A + bar B := by
  ext i j; simp [bar]

@[simp] lemma bar_sub (A B : Matrix d d ℂ) : bar (A - B) = bar A - bar B := by
  ext i j; simp [bar]

@[simp] lemma bar_one : bar (1 : Matrix d d ℂ) = 1 := by
  ext i j; simp [bar, Matrix.one_apply]

@[simp] lemma bar_zero : bar (0 : Matrix d d ℂ) = 0 := by
  ext i j; simp [bar]

@[simp] lemma bar_bar (A : Matrix d d ℂ) : bar (bar A) = A := by
  ext i j; simp [bar]

@[simp] lemma bar_conjTranspose (A : Matrix d d ℂ) :
    bar A.conjTranspose = (bar A).conjTranspose := by
  ext i j; simp [bar, Matrix.conjTranspose_apply]

lemma bar_trace (A : Matrix d d ℂ) : (bar A).trace = star A.trace := by
  simp [bar, Matrix.trace, star_sum]

lemma bar_eq_of_transpose (A : Matrix d d ℂ)
    (hA : A.transpose = A.conjTranspose) : bar A = A := by
  ext i j
  exact (congrFun₂ hA j i).symm

lemma fullGridH_bar (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ)
    (hU : ∀ i, (U i).transpose = (U i).conjTranspose) (L : ℕ) (γ : ℝ) :
    bar (ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ).mat =
      (ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ).mat := by
  apply bar_eq_of_transpose
  rw [(ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ).H.eq]
  exact fullGridH_transpose C₁ hC₁ hk C₂ U hU L γ

lemma suppressorK_bar {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hH : bar H = H) (hU : ∀ i, bar (U i) = U i) (i j : Fin k) :
    bar (EntropyLemmas.BellAlgebra.suppressorK H U i j) =
      EntropyLemmas.BellAlgebra.suppressorK H U i j := by
  unfold EntropyLemmas.BellAlgebra.suppressorK
  by_cases hij : i = j <;> simp [hij, hH, hU]

/-- The actual channel equals its complex conjugate when the tuple is real. -/
lemma fullGridChannel_real {n : ℕ} (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (hreal : ∀ i, (U i).transpose = (U i).conjTranspose)
    (L : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (MainChannel.fullGridChannel C₁ hC₁ hk C₂ U hU L γ hγ hγ1).map X =
      ((MainChannel.fullGridChannel C₁ hC₁ hk C₂ U hU L γ hγ hγ1).map
        (X.map (starRingEnd ℂ))).map (starRingEnd ℂ) := by
  have hH := fullGridH_bar C₁ hC₁ hk C₂ U hreal L γ
  have hUr := fun i => bar_eq_of_transpose (U i) (hreal i)
  ext i j
  simp only [Matrix.map_apply, MainChannel.fullGridChannel_entry,
    EntropyLemmas.BellAlgebra.channelEntry, map_div₀, map_natCast]
  change _ = star ((EntropyLemmas.BellAlgebra.suppressorK _ U j i * bar X).trace) / _
  rw [← bar_trace, bar_mul, suppressorK_bar _ U hH hUr, bar_bar]

#print axioms filter_transpose
#print axioms fullGridChannel_real

end MainReal
