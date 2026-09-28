import QuantumInfo.Channels.CPTP
import BellAlgebra

/-!
# The actual tensor-product channel on a Bell input

The definitions in `BellAlgebra` are connected here to Physlib's bundled
completely positive trace-preserving maps and normalized pure Bell state.
The entry hypotheses are defining equalities for a channel and its conjugate.
-/

open scoped BigOperators
open scoped InnerProductSpace RealInnerProductSpace

namespace EntropyLemmas.TensorBridge

open EntropyLemmas.BellAlgebra

variable {n k : ℕ}

/-- The usual full defining equality of the conjugate channel implies the
matrix-unit relation used below. Thus that relation is not an additional
restriction on the channel. -/
lemma conjugate_matrix_unit_entries
    (Φ Φbar : CPTPMap (Fin n) (Fin k))
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hΦ : ∀ X i j, Φ.map X i j = channelEntry K X i j)
    (hconj : ∀ X, Φbar.map X =
      (Φ.map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ))
    (x y : Fin n) (a b : Fin k) :
    Φbar.map (Matrix.single x y 1) a b =
      star (channelEntry K (Matrix.single x y 1) a b) := by
  rw [hconj]
  simp only [Matrix.map_single, map_one, Matrix.map_apply, hΦ]
  rfl

/-- The matrix entries of the normalized Bell density matrix. -/
lemma bell_input_entry [Nonempty (Fin n)] (i a j b : Fin n) :
    (MState.pure (Ket.MES (Fin n))).m (i, a) (j, b) =
      if i = a ∧ j = b then (n : ℂ)⁻¹ else 0 := by
  simp only [MState.pure_apply, Ket.MES, Ket.apply, Fintype.card_fin]
  by_cases hia : i = a <;> by_cases hjb : j = b
  · simp only [hia, hjb, and_self, ↓reduceIte,
      one_div, map_inv₀, Complex.conj_ofReal]
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    simp only [Complex.ofReal_natCast]
  · simp [hia, hjb]
  · simp [hia, hjb]
  · simp [hia, hjb]

/-- Applying the actual tensor product to the Bell state contracts matching
input matrix units. This statement uses the defining relation of a conjugate
channel only on matrix units, where entrywise conjugation fixes the input. -/
lemma product_bell_entry_eq_contraction [Nonempty (Fin n)]
    (Φ Φbar : CPTPMap (Fin n) (Fin k))
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hΦ : ∀ X i j, Φ.map X i j = channelEntry K X i j)
    (hbar : ∀ x y a b,
      Φbar.map (Matrix.single x y 1) a b =
        star (channelEntry K (Matrix.single x y 1) a b))
    (i a j b : Fin k) :
    ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))).m (i, a) (j, b) =
      bellOutputContraction K i a j b := by
  change (Φ.map.kron Φbar.map) (MState.pure (Ket.MES (Fin n))).m
      (i, a) (j, b) = _
  rw [MatrixMap.kron_def]
  simp_rw [bell_input_entry]
  simp only [ite_and, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  simp only [hΦ, hbar, bellOutputContraction, div_eq_mul_inv, Finset.sum_mul]

/-- Exact entries of the physical Bell output, expressed by traces of the
adjoint-channel coefficients. -/
lemma product_bell_entry_eq_sigmaEntry [Nonempty (Fin n)]
    (Φ Φbar : CPTPMap (Fin n) (Fin k))
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hΦ : ∀ X i j, Φ.map X i j = channelEntry K X i j)
    (hbar : ∀ x y a b,
      Φbar.map (Matrix.single x y 1) a b =
        star (channelEntry K (Matrix.single x y 1) a b))
    (hsym : ∀ i j, (K i j).conjTranspose = K j i)
    (i a j b : Fin k) :
    ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))).m (i, a) (j, b) =
      sigmaEntry K i a j b := by
  rw [product_bell_entry_eq_contraction Φ Φbar K hΦ hbar]
  exact bellOutputContraction_eq_sigmaEntry K hsym i a j b

/-- Every computational-basis diagonal entry of the physical Bell output is
`1/k²` when the adjoint coefficients have identity diagonal. -/
lemma product_bell_diagonal [Nonempty (Fin n)]
    (Φ Φbar : CPTPMap (Fin n) (Fin k))
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hΦ : ∀ X i j, Φ.map X i j = channelEntry K X i j)
    (hbar : ∀ x y a b,
      Φbar.map (Matrix.single x y 1) a b =
        star (channelEntry K (Matrix.single x y 1) a b))
    (hsym : ∀ i j, (K i j).conjTranspose = K j i)
    (hdiag : ∀ i, K i i = 1) (hn : n ≠ 0) (i a : Fin k) :
    ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))).m (i, a) (i, a) =
      1 / (k : ℂ) ^ 2 := by
  rw [product_bell_entry_eq_sigmaEntry Φ Φbar K hΦ hbar hsym]
  exact sigmaEntry_diagonal K hdiag hn i a

/-- The physical output Bell overlap is the normalized sum of entries on the
diagonal tensor subspace. -/
lemma trace_bell_mul [Nonempty (Fin k)]
    (S : Matrix (Fin k × Fin k) (Fin k × Fin k) ℂ) :
    Matrix.trace ((MState.pure (Ket.MES (Fin k))).m * S) =
      (∑ i : Fin k, ∑ j : Fin k, S (i, i) (j, j)) / (k : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, bell_input_entry]
  simp only [ite_and, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.mul_sum, mul_comm]

/-- The trace overlap of the bundled tensor-channel output is the exact
Bell-overlap expression proved in `BellAlgebra`. -/
lemma product_bell_overlap [Nonempty (Fin n)] [Nonempty (Fin k)]
    (Φ Φbar : CPTPMap (Fin n) (Fin k))
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hΦ : ∀ X i j, Φ.map X i j = channelEntry K X i j)
    (hbar : ∀ x y a b,
      Φbar.map (Matrix.single x y 1) a b =
        star (channelEntry K (Matrix.single x y 1) a b))
    (hsym : ∀ i j, (K i j).conjTranspose = K j i) :
    Matrix.trace ((MState.pure (Ket.MES (Fin k))).m *
      ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))).m) =
        bellOverlap K := by
  rw [trace_bell_mul]
  simp only [bellOverlap, product_bell_entry_eq_sigmaEntry Φ Φbar K hΦ hbar hsym]

/-- Real Hermitian inner-product version of the Bell-overlap bridge. -/
lemma product_bell_inner [Nonempty (Fin n)] [Nonempty (Fin k)]
    (Φ Φbar : CPTPMap (Fin n) (Fin k))
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hΦ : ∀ X i j, Φ.map X i j = channelEntry K X i j)
    (hbar : ∀ x y a b,
      Φbar.map (Matrix.single x y 1) a b =
        star (channelEntry K (Matrix.single x y 1) a b))
    (hsym : ∀ i j, (K i j).conjTranspose = K j i) :
    ⟪((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))).M,
      (MState.pure (Ket.MES (Fin k))).M⟫_ℝ = (bellOverlap K).re := by
  rw [HermitianMat.inner_eq_re_trace]
  simp only [MState.mat_M]
  rw [Matrix.trace_mul_comm]
  rw [product_bell_overlap Φ Φbar K hΦ hbar hsym]
  rfl

/-- Projection onto the span of `|ii⟩`, of dimension `k`. -/
noncomputable def diagonalTensorProjection (k : ℕ) :
    HermitianMat (Fin k × Fin k) ℂ :=
  HermitianMat.diagonal ℂ (fun ij => if ij.1 = ij.2 then 1 else 0)

/-- Projection onto the normalized Bell vector. -/
noncomputable def bellProjection (k : ℕ) [Nonempty (Fin k)] :
    HermitianMat (Fin k × Fin k) ℂ :=
  (MState.pure (Ket.MES (Fin k))).M

lemma diagonalTensorProjection_idempotent (k : ℕ) :
    (diagonalTensorProjection k).mat * (diagonalTensorProjection k).mat =
      (diagonalTensorProjection k).mat := by
  simp only [diagonalTensorProjection, HermitianMat.diagonal_mat,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext ij
  by_cases h : ij.1 = ij.2 <;> simp [h]

lemma bellProjection_idempotent (k : ℕ) [Nonempty (Fin k)] :
    (bellProjection k).mat * (bellProjection k).mat = (bellProjection k).mat := by
  exact MState.pure_mul_self (Ket.MES (Fin k))

lemma diagonalTensorProjection_mul_bellProjection (k : ℕ) [Nonempty (Fin k)] :
    (diagonalTensorProjection k).mat * (bellProjection k).mat =
      (bellProjection k).mat := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [diagonalTensorProjection, HermitianMat.diagonal_mat,
    Matrix.diagonal_mul, bellProjection, MState.mat_M, bell_input_entry]
  by_cases h : i = a <;> simp [h]

lemma bellProjection_mul_diagonalTensorProjection (k : ℕ) [Nonempty (Fin k)] :
    (bellProjection k).mat * (diagonalTensorProjection k).mat =
      (bellProjection k).mat := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [diagonalTensorProjection, HermitianMat.diagonal_mat,
    Matrix.mul_diagonal, bellProjection, MState.mat_M, bell_input_entry]
  by_cases h : j = b <;> simp [h]

lemma diagonalTensorProjection_trace (k : ℕ) :
    (diagonalTensorProjection k).trace = k := by
  unfold diagonalTensorProjection
  rw [HermitianMat.trace_diagonal, Fintype.sum_prod_type]
  simp

lemma bellProjection_trace (k : ℕ) [Nonempty (Fin k)] :
    (bellProjection k).trace = 1 := by
  exact (MState.pure (Ket.MES (Fin k))).tr

/-- A uniform computational-basis diagonal fixes the mass in the diagonal
tensor subspace to exactly `1/k`. -/
lemma inner_diagonalTensorProjection_of_uniform
    (σ : MState (Fin k × Fin k)) (hk : k ≠ 0)
    (hdiag : ∀ i a, σ.m (i, a) (i, a) = 1 / (k : ℂ)^2) :
    ⟪σ.M, diagonalTensorProjection k⟫_ℝ = 1 / (k : ℝ) := by
  rw [HermitianMat.inner_eq_re_trace]
  simp only [MState.mat_M, diagonalTensorProjection, HermitianMat.diagonal_mat,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Fintype.sum_prod_type]
  simp only [hdiag]
  simp only [apply_ite, map_one, map_zero, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hcancel : (k : ℂ) * (1 / (k : ℂ)^2) = 1 / (k : ℂ) := by
    field_simp [hkC]
  rw [hcancel]
  simp

/-- Exact diagonal-subspace mass for the physical tensor-channel output. -/
lemma product_bell_diagonal_mass [Nonempty (Fin n)]
    (Φ Φbar : CPTPMap (Fin n) (Fin k))
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hΦ : ∀ X i j, Φ.map X i j = channelEntry K X i j)
    (hbar : ∀ x y a b,
      Φbar.map (Matrix.single x y 1) a b =
        star (channelEntry K (Matrix.single x y 1) a b))
    (hsym : ∀ i j, (K i j).conjTranspose = K j i)
    (hdiag : ∀ i, K i i = 1) (hn : n ≠ 0) (hk : k ≠ 0) :
    ⟪((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))).M,
      diagonalTensorProjection k⟫_ℝ = 1 / (k : ℝ) := by
  apply inner_diagonalTensorProjection_of_uniform _ hk
  exact product_bell_diagonal Φ Φbar K hΦ hbar hsym hdiag hn

#print axioms product_bell_entry_eq_sigmaEntry
#print axioms product_bell_inner
#print axioms product_bell_diagonal_mass

end EntropyLemmas.TensorBridge
