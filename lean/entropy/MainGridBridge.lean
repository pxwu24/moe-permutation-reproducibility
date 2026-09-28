import AdderTrace
import ActualGridFilterLower
import MainFilterParameters
import MainAdderTuple

/-! The two formal representations of the Gaussian grid and filter coincide. -/
noncomputable section
open scoped BigOperators

namespace MainGridBridge

variable {k : ℕ}

lemma gaussian_iff (z : ℂ) :
    (∃ p q : ℤ, z = (p : ℂ) + (q : ℂ) * Complex.I) ↔
      (∃ p : ℤ, z.re = p) ∧ (∃ q : ℤ, z.im = q) := by
  constructor
  · rintro ⟨p, q, rfl⟩
    exact ⟨⟨p, by simp⟩, ⟨q, by simp⟩⟩
  · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    refine ⟨p, q, ?_⟩
    apply Complex.ext <;> simp [hp, hq]

lemma hermitian_entries (W : HermitianMat (Fin k) ℂ) (i j : Fin k) :
    W j i = star (W i j) := (congrFun (congrFun W.H j) i).symm

lemma norm_sq_trace (W : HermitianMat (Fin k) ℂ) :
    ‖W‖ ^ 2 = (Matrix.trace (W.mat ^ 2)).re := by
  rw [← AdderTrace.MatrixGrid.energy_eq_trace_sq W.mat (hermitian_entries W)]
  rw [GaussianHermitianGrid.norm_sq_entries]
  simp [AdderTrace.MatrixGrid.energy, Complex.normSq_eq_norm_sq]

lemma inGrid_iff_mem (C₁ : ℝ) (hk : 0 < k) (hC₁ : 0 < C₁)
    (W : HermitianMat (Fin k) ℂ) :
    GaussianHermitianGrid.InGrid C₁ W ↔
      W.mat ∈ AdderTrace.MatrixGrid.fullGrid k C₁ hk hC₁ := by
  rw [AdderTrace.MatrixGrid.mem_fullGrid]
  unfold GaussianHermitianGrid.InGrid AdderTrace.MatrixGrid.IntegralEntries
  rw [norm_sq_trace]
  constructor
  · rintro ⟨hd, hg, hl, hu⟩
    exact ⟨hd, hermitian_entries W, fun i j => (gaussian_iff _).1 (hg i j), hl, hu⟩
  · rintro ⟨hd, _, hg, hl, hu⟩
    exact ⟨hd, fun i j => (gaussian_iff _).2 (hg i j), hl, hu⟩

/-- Forgetting the Hermitian wrapper bijects the two actual full grids. -/
def gridEquiv (C₁ : ℝ) (hk : 0 < k) (hC₁ : 0 < C₁) :
    {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W} ≃
      ↥(AdderTrace.MatrixGrid.fullGrid k C₁ hk hC₁) where
  toFun W := ⟨W.val.mat, (inGrid_iff_mem C₁ hk hC₁ W.val).1 W.property⟩
  invFun W :=
    let hW := (AdderTrace.MatrixGrid.mem_fullGrid k C₁ hk hC₁ W.val).1 W.property
    let V : HermitianMat (Fin k) ℂ := ⟨W.val, by
      ext i j
      exact (hW.2.1 j i).symm⟩
    ⟨V, (inGrid_iff_mem C₁ hk hC₁ V).2 W.property⟩
  left_inv W := by apply Subtype.ext; rfl
  right_inv W := by apply Subtype.ext; rfl

variable {d : Type*} [Fintype d] [DecidableEq d]

lemma observable_eq_momentMatrix (U : Fin k → Matrix d d ℂ)
    (W : HermitianMat (Fin k) ℂ) (hdiag : ∀ i, W i i = 0) :
    (GaussianSignCoefficient.observable U W).mat = AdderTrace.momentMatrix U W.mat := by
  unfold GaussianSignCoefficient.observable AdderTrace.momentMatrix
  change (∑ i, ∑ j, W i j • ((U i).conjTranspose * U j)) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = j
  · subst j
    simp [hdiag]
  · simp [h]

/-- Equality of the actual finite sums, including their normalization and powers. -/
theorem fullGridFilter_mat (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ) (L : ℕ) :
    (ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L).mat =
      AdderTrace.filterMatrix
        (AdderTrace.MatrixGrid.fullGrid k C₁ (by omega) (by linarith)) U (C₂ * k) L := by
  classical
  let G := {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W}
  let : Fintype G := (GaussianHermitianGrid.grid_finite C₁ (by linarith) (by omega)).fintype
  let S := AdderTrace.MatrixGrid.fullGrid k C₁ (by omega) (by linarith)
  let e : G ≃ ↥S := gridEquiv C₁ (by omega) (by linarith)
  let f := fun W : Matrix (Fin k) (Fin k) ℂ =>
    ((((C₂ * (k : ℝ))⁻¹ : ℝ) : ℂ) • AdderTrace.momentMatrix U W) ^ (2 * L)
  have hterm (W : G) :
      (((C₂ * (k : ℝ))⁻¹ • GaussianSignCoefficient.observable U W.val) ^ (2 * L)).mat =
        f (e W).val := by
    rw [HermitianMat.mat_pow, HermitianMat.mat_smul,
      observable_eq_momentMatrix U W.val W.property.1]
    rfl
  unfold ActualGridFilterLower.fullGridFilter FiniteFilterSupport.filter
  rw [HermitianMat.mat_finset_sum]
  change (∑ W : G, _) = ∑ W ∈ S, f W
  simp_rw [hterm]
  rw [e.sum_comp (fun W : ↥S => f W.val)]
  exact Finset.sum_coe_sort S f

variable {d' : Type*} [Fintype d'] [DecidableEq d']

lemma momentMatrix_submatrix (e : d' ≃ d) (U : Fin k → Matrix d d ℂ)
    (W : Matrix (Fin k) (Fin k) ℂ) :
    AdderTrace.momentMatrix (fun i => (U i).submatrix e e) W =
      (AdderTrace.momentMatrix U W).submatrix e e := by
  let a := Matrix.reindexAlgEquiv ℂ ℂ e.symm
  change AdderTrace.momentMatrix (fun i => a (U i)) W = a (AdderTrace.momentMatrix U W)
  have hstar (X : Matrix d d ℂ) : (a X).conjTranspose = a X.conjTranspose := by
    ext i j
    rfl
  unfold AdderTrace.momentMatrix
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [hstar]

lemma filterMatrix_submatrix (e : d' ≃ d)
    (S : Finset (Matrix (Fin k) (Fin k) ℂ)) (U : Fin k → Matrix d d ℂ)
    (c : ℝ) (L : ℕ) :
    AdderTrace.filterMatrix S (fun i => (U i).submatrix e e) c L =
      (AdderTrace.filterMatrix S U c L).submatrix e e := by
  let a := Matrix.reindexAlgEquiv ℂ ℂ e.symm
  have hm (W : Matrix (Fin k) (Fin k) ℂ) :
      AdderTrace.momentMatrix (fun i => (U i).submatrix e e) W =
        a (AdderTrace.momentMatrix U W) := momentMatrix_submatrix e U W
  change AdderTrace.filterMatrix S (fun i => (U i).submatrix e e) c L =
    a (AdderTrace.filterMatrix S U c L)
  unfold AdderTrace.filterMatrix
  simp only [map_sum, map_pow, map_smul, hm]

lemma trace_submatrix (e : d' ≃ d) (X : Matrix d d ℂ) :
    Matrix.trace (X.submatrix e e) = Matrix.trace X := by
  change (∑ i : d', X (e i) (e i)) = ∑ i : d, X i i
  exact e.sum_comp (fun i => X i i)

/-- Changing the finite input labels preserves the full filter trace. -/
theorem fullGridFilter_trace_submatrix (e : d' ≃ d)
    (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ) (L : ℕ) :
    (ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂
      (fun i => (U i).submatrix e e) L).trace =
      (ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L).trace := by
  change (Matrix.trace (ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂
      (fun i => (U i).submatrix e e) L).mat).re =
    (Matrix.trace (ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L).mat).re
  rw [fullGridFilter_mat, fullGridFilter_mat, filterMatrix_submatrix, trace_submatrix]

lemma k_ge_two (r : ℕ) (hr : 1 ≤ r) : 2 ≤ MainFilterParameters.M ^ r := by
  have h := le_self_pow₀ (by norm_num : (1 : ℕ) ≤ MainFilterParameters.M)
    (by omega : r ≠ 0)
  exact le_trans (by norm_num) h

/-- The trace bound transfers to the exact Hermitian full-grid filter. -/
theorem fullGridFilter_small (r : ℕ) (hr : 1 ≤ r) :
    (ActualGridFilterLower.fullGridFilter MainFilterParameters.C₁ (by norm_num)
      (k_ge_two r hr) (MainFilterParameters.C₂ r)
      (AdderTrace.finAdderMatrix (2 ^ MainFilterParameters.q r) r MainFilterParameters.M)
      (MainFilterParameters.L r)).trace /
        (MainFilterParameters.Q r : ℝ) ^ (2 * r) < MainFilterParameters.E := by
  change (Matrix.trace (ActualGridFilterLower.fullGridFilter _ _ _ _ _ _).mat).re / _ < _
  rw [fullGridFilter_mat]
  exact MainFilterParameters.prescribedFilter_small r hr

/-- The same trace error for the exact enumerated tensor family used by the
channel and entropy formalizations. -/
theorem enumerated_fullGridFilter_small (r : ℕ) (hr : 1 ≤ r) :
    (ActualGridFilterLower.fullGridFilter MainFilterParameters.C₁ (by norm_num)
      (k_ge_two r hr) (MainFilterParameters.C₂ r)
      (ActualTensorBasis.enumeratedTuple
        (MainAdderTuple.inputEquiv (2 ^ MainFilterParameters.q r) r)
        (MainAdderTuple.generator (2 ^ MainFilterParameters.q r) MainFilterParameters.M))
      (MainFilterParameters.L r)).trace /
        (MainFilterParameters.Q r : ℝ) ^ (2 * r) < MainFilterParameters.E := by
  have hU : ActualTensorBasis.enumeratedTuple
        (MainAdderTuple.inputEquiv (2 ^ MainFilterParameters.q r) r)
        (MainAdderTuple.generator (2 ^ MainFilterParameters.q r) MainFilterParameters.M) =
      fun i => (AdderTrace.finAdderMatrix (2 ^ MainFilterParameters.q r) r MainFilterParameters.M i).submatrix (MainAdderTuple.inputEquiv (2 ^ MainFilterParameters.q r) r)
          (MainAdderTuple.inputEquiv (2 ^ MainFilterParameters.q r) r) := by
    funext i
    exact MainAdderTuple.enumeratedTuple_eq_finAdderMatrix _ _ _ i
  rw [hU, fullGridFilter_trace_submatrix]
  exact fullGridFilter_small r hr

end MainGridBridge
