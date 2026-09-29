import MainPauli
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped BigOperators Kronecker

namespace MainPauliTensor
open MainPauli

abbrev Index (m : ℕ) := Bits m × Bits m

def tensorPauli {m : ℕ} (v : Index m × Index m) :
    Matrix (Bits m × Bits m) (Bits m × Bits m) ℂ :=
  pauli v.1.1 v.1.2 ⊗ₖ pauli v.2.1 v.2.2

def tensorConjugate {m : ℕ} (v : Index m × Index m) :
    Matrix (Bits m × Bits m) (Bits m × Bits m) ℂ →ₗ[ℂ]
      Matrix (Bits m × Bits m) (Bits m × Bits m) ℂ where
  toFun A := tensorPauli v * A * (tensorPauli v).conjTranspose
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' z A := by simp

def tensorAverage (m : ℕ) :
    Matrix (Bits m × Bits m) (Bits m × Bits m) ℂ →ₗ[ℂ]
      Matrix (Bits m × Bits m) (Bits m × Bits m) ℂ :=
  (Fintype.card (Index m × Index m) : ℂ)⁻¹ • ∑ v, tensorConjugate v

lemma tensorAverage_product (m : ℕ)
    (A B : Matrix (Bits m) (Bits m) ℂ) :
    tensorAverage m (A ⊗ₖ B) =
      MainPauli.average (fun v : Index m => v) A ⊗ₖ
        MainPauli.average (fun v : Index m => v) B := by
  simp only [tensorAverage, MainPauli.average, LinearMap.smul_apply,
    LinearMap.sum_apply, tensorConjugate, MainPauli.conjugate,
    LinearMap.coe_mk, AddHom.coe_mk, tensorPauli, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Fintype.card_prod,
    Nat.cast_mul, mul_inv_rev]
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.kronecker_apply,
    smul_eq_mul]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum]
  ring

def traceProjection (m : ℕ) :
    Matrix (Bits m × Bits m) (Bits m × Bits m) ℂ →ₗ[ℂ]
      Matrix (Bits m × Bits m) (Bits m × Bits m) ℂ where
  toFun A := ((Fintype.card (Bits m × Bits m) : ℂ)⁻¹ * Matrix.trace A) • 1
  map_add' A B := by simp [Matrix.trace_add, mul_add, add_smul]
  map_smul' z A := by simp [Matrix.trace_smul, smul_smul, mul_left_comm]

lemma tensorAverage_eq_projection_product (m : ℕ)
    (A B : Matrix (Bits m) (Bits m) ℂ) :
    tensorAverage m (A ⊗ₖ B) = traceProjection m (A ⊗ₖ B) := by
  rw [tensorAverage_product, pauli_twirl, pauli_twirl]
  simp only [traceProjection, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
    Matrix.one_kronecker_one, Matrix.trace_kronecker,
    Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  congr 1
  ring

/-- The exact tensor Pauli twirl, for an arbitrary (possibly entangled) matrix. -/
theorem tensor_pauli_twirl (m : ℕ)
    (A : Matrix (Bits m × Bits m) (Bits m × Bits m) ℂ) :
    tensorAverage m A =
      ((Fintype.card (Bits m × Bits m) : ℂ)⁻¹ * Matrix.trace A) • 1 := by
  change tensorAverage m A = traceProjection m A
  rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : Matrix.single i j (A i j) =
      Matrix.single i.1 j.1 (A i j) ⊗ₖ Matrix.single i.2 j.2 (1 : ℂ) := by
    simp [Matrix.single_kronecker_single]
  rw [hs]
  exact tensorAverage_eq_projection_product m _ _

end MainPauliTensor
