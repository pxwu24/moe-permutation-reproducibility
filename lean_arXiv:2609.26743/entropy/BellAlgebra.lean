import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-!
# A. Bell-output matrix algebra

Exact finite-matrix identities for the suppressed complementary channel.
All traces are unnormalized. The output is represented entrywise so that
the normalization and diagonal/off-diagonal split are explicit.
-/

open scoped BigOperators
open Matrix

namespace EntropyLemmas.BellAlgebra

variable {n k : ℕ}

/-- Entries of the channel determined by its adjoint coefficients `K`. -/
noncomputable def channelEntry
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) : ℂ :=
  Matrix.trace (K j i * X) / (k : ℂ)

/-- Expansion of the conjugate-channel output using
`ωₙ = (1/n) ∑ x y, Eₓᵧ ⊗ Eₓᵧ`. -/
noncomputable def bellOutputContraction
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (i a j b : Fin k) : ℂ :=
  (∑ x, ∑ y, channelEntry K (Matrix.single x y 1) i j *
    star (channelEntry K (Matrix.single x y 1) a b)) / (n : ℂ)

/-- Matrix entries of the conjugate-channel output on the normalized Bell input,
written in terms of the adjoint-channel coefficient matrices `K`. -/
noncomputable def sigmaEntry
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (i a j b : Fin k) : ℂ :=
  Matrix.trace (K j i * K a b) / ((n : ℂ) * (k : ℂ) ^ 2)

/-- Overlap of the entrywise Bell output with the normalized output Bell vector. -/
noncomputable def bellOverlap
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (∑ i, ∑ j, sigmaEntry K i i j j) / (k : ℂ)

/-- The sum over ordered distinct output indices. -/
noncomputable def offDiagonalSum (f : Fin k → Fin k → ℂ) : ℂ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, f i j

/-- Evaluating the channel on an input matrix unit fixes the trace indices. -/
lemma channelEntry_matrixUnit
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin k) (x y : Fin n) :
    channelEntry K (Matrix.single x y 1) i j = K j i y x / (k : ℂ) := by
  unfold channelEntry
  rw [Matrix.trace_mul_comm]
  simp [Matrix.trace_single_mul]

/-- Trace duality between the output channel matrix and its coefficient sum. -/
lemma channelEntry_tracePairing
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin k) (Fin k) ℂ) :
    Matrix.trace (Matrix.of (fun i j ↦ channelEntry K X i j) * W) =
      Matrix.trace (X * (∑ i, ∑ j, W i j • K i j)) / (k : ℂ) := by
  have hleft : Matrix.trace (Matrix.of (fun i j ↦ channelEntry K X i j) * W) =
      ∑ i, ∑ j, channelEntry K X j i * W i j := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
  rw [hleft]
  simp_rw [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold channelEntry
  rw [Matrix.trace_mul_comm]
  ring

/-- The coefficient contraction is exactly the trace-product formula for the
Bell-output entries. -/
lemma bellOutputContraction_eq_sigmaEntry
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hsym : ∀ i j, (K i j).conjTranspose = K j i) (i a j b : Fin k) :
    bellOutputContraction K i a j b = sigmaEntry K i a j b := by
  have hterm (x y : Fin n) :
      (K j i y x / (k : ℂ)) * star (K b a y x / (k : ℂ)) =
        (K j i y x * K a b x y) / (k : ℂ) ^ 2 := by
    have hreverse : star (K b a y x) = K a b x y := by
      simpa only [Matrix.conjTranspose_apply] using
        congrFun (congrFun (hsym b a) x) y
    simp only [star_div₀, star_natCast, hreverse]
    rw [div_mul_div_comm]
    congr 1
    ring
  unfold bellOutputContraction
  simp_rw [channelEntry_matrixUnit, hterm, ← Finset.sum_div]
  rw [div_div]
  have hsum : (∑ x, ∑ y, K j i y x * K a b x y) =
      Matrix.trace (K j i * K a b) := by
    rw [Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [hsum]
  unfold sigmaEntry
  congr 1
  ring

/-- Uniform adjoint diagonal implies a uniform diagonal for the Bell output. -/
lemma sigmaEntry_diagonal
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hdiag : ∀ i, K i i = 1) (hn : n ≠ 0) (i a : Fin k) :
    sigmaEntry K i a i a = 1 / (k : ℂ) ^ 2 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [sigmaEntry, hdiag, one_mul, Matrix.trace_one, Fintype.card_fin]
  rw [div_mul_eq_div_div, div_self hn']

/-- The Bell normalization contributes one factor of `k` in addition to the
two channel factors. -/
lemma bellOverlap_trace_sum
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ) :
    bellOverlap K =
      (∑ i, ∑ j, Matrix.trace (K i j * K j i)) / ((n : ℂ) * (k : ℂ) ^ 3) := by
  unfold bellOverlap sigmaEntry
  simp_rw [← Finset.sum_div]
  rw [div_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact Matrix.trace_mul_comm _ _
  · ring

/-- Splitting the exact Bell overlap into the known diagonal contribution and
the ordered off-diagonal trace sum. -/
lemma bellOverlap_diagonal_split
    (K : Fin k → Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hdiag : ∀ i, K i i = 1) (hn : n ≠ 0) (hk : k ≠ 0) :
    bellOverlap K = 1 / (k : ℂ) ^ 2 +
      offDiagonalSum (fun i j ↦ Matrix.trace (K i j * K j i)) /
        ((n : ℂ) * (k : ℂ) ^ 3) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hrow (i : Fin k) :
      (∑ j, Matrix.trace (K i j * K j i)) =
        (∑ j ∈ Finset.univ.erase i, Matrix.trace (K i j * K j i)) + (n : ℂ) := by
    simpa only [hdiag, one_mul, Matrix.trace_one, Fintype.card_fin] using
      (Finset.sum_erase_add Finset.univ
        (fun j ↦ Matrix.trace (K i j * K j i)) (Finset.mem_univ i)).symm
  rw [bellOverlap_trace_sum]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold offDiagonalSum
  field_simp
  ring

/-!
## A.1. Suppressor coefficients
-/

/-- Adjoint-channel coefficient matrices for a positive suppressor `H`.
Hermiticity and positivity are assumptions in the corresponding lemmas. -/
noncomputable def suppressorK (H : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) :
    Matrix (Fin n) (Fin n) ℂ :=
  H * (U i).conjTranspose * U j * H + if i = j then 1 - H * H else 0

/-- The coefficient definition agrees with the channel formula using
`Tr(Uᵢ H X H Uⱼ†)` and the diagonal register correction. -/
lemma channelEntry_suppressor (H X : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) :
    channelEntry (suppressorK H U) X i j =
      (Matrix.trace (U i * H * X * H * (U j).conjTranspose) +
        if i = j then Matrix.trace ((1 - H * H) * X) else 0) / (k : ℂ) := by
  have hcore : Matrix.trace (H * (U j).conjTranspose * U i * H * X) =
      Matrix.trace (U i * H * X * H * (U j).conjTranspose) := by
    calc
      _ = Matrix.trace ((H * (U j).conjTranspose) * (U i * H * X)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((U i * H * X) * (H * (U j).conjTranspose)) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; noncomm_ring
  unfold channelEntry suppressorK
  rw [Matrix.add_mul, Matrix.trace_add, hcore]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

/-- A zero-diagonal test matrix removes the register correction from the adjoint
coefficient sum, leaving the suppressed unitary polynomial. -/
lemma suppressorK_zeroDiagonal_sum (H : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (W : Matrix (Fin k) (Fin k) ℂ) (hW : ∀ i, W i i = 0) :
    (∑ i, ∑ j, W i j • suppressorK H U i j) =
      H * (∑ i, ∑ j, W i j • ((U i).conjTranspose * U j)) * H := by
  simp_rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp only [hW, zero_smul, mul_zero, zero_mul]
  · simp only [suppressorK, if_neg hij, add_zero]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    noncomm_ring

/-- The register term makes every diagonal adjoint coefficient exactly the identity. -/
lemma suppressorK_diagonal (H : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1) (i : Fin k) :
    suppressorK H U i i = 1 := by
  unfold suppressorK
  rw [if_pos rfl, mul_assoc H (U i).conjTranspose (U i), hU i, mul_one]
  noncomm_ring

/-- Reversing the output indices conjugate-transposes an adjoint coefficient. -/
lemma suppressorK_conjTranspose (H : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hH : H.conjTranspose = H) (i j : Fin k) :
    (suppressorK H U i j).conjTranspose = suppressorK H U j i := by
  by_cases hij : i = j
  · subst j
    simp [suppressorK, hH, mul_assoc]
  · simp [suppressorK, hij, Ne.symm hij, hH, mul_assoc]

/-- Cyclicity of trace moves the outside suppressors together without requiring
the suppressor to commute with any unitary. -/
lemma suppressorK_offDiagonal_trace (H : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) (hij : i ≠ j) :
    Matrix.trace (suppressorK H U i j * suppressorK H U j i) =
      Matrix.trace ((H * H) * ((U i).conjTranspose * U j) *
        (H * H) * ((U j).conjTranspose * U i)) := by
  simp only [suppressorK, if_neg hij, if_neg (Ne.symm hij), add_zero]
  calc
    _ = Matrix.trace ((H * (U i).conjTranspose * U j * H * H *
        (U j).conjTranspose * U i) * H) := by congr 1; noncomm_ring
    _ = Matrix.trace (H * (H * (U i).conjTranspose * U j * H * H *
        (U j).conjTranspose * U i)) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1; noncomm_ring

/-- Exact Bell overlap for the suppressed complementary channel. -/
lemma suppressor_bellOverlap (H : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1) (hn : n ≠ 0) (hk : k ≠ 0) :
    bellOverlap (suppressorK H U) = 1 / (k : ℂ) ^ 2 +
      offDiagonalSum (fun i j ↦ Matrix.trace ((H * H) *
        ((U i).conjTranspose * U j) * (H * H) * ((U j).conjTranspose * U i))) /
        ((n : ℂ) * (k : ℂ) ^ 3) := by
  rw [bellOverlap_diagonal_split _ (suppressorK_diagonal H U hU) hn hk]
  congr 2
  unfold offDiagonalSum
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact suppressorK_offDiagonal_trace H U i j (Ne.symm (Finset.mem_erase.mp hj).1)

/-- Uniform computational-basis diagonal of the suppressed Bell output. -/
lemma suppressor_sigmaEntry_diagonal (H : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1) (hn : n ≠ 0) (i a : Fin k) :
    sigmaEntry (suppressorK H U) i a i a = 1 / (k : ℂ) ^ 2 := by
  exact sigmaEntry_diagonal _ (suppressorK_diagonal H U hU) hn i a

end EntropyLemmas.BellAlgebra
