import TensorMarginalEntropy
import Mathlib.Logic.Equiv.Prod

/-!
# A. Actual tensor tuples and cancellation in every output coordinate

The tensor tuple is the actual finite Pi-product of its unitary factors.
The suppressor remains an arbitrary global matrix throughout.
-/

noncomputable section
open scoped BigOperators Kronecker

namespace ActualTensorTuple

variable {a d : Type*} [Fintype a] [DecidableEq a]
  [Fintype d] [DecidableEq d]

/-- Multiplication factors coordinatewise for the finite tensor matrix. -/
lemma piProd_mul (A B : a → Matrix d d ℂ) :
    Matrix.piProd A * Matrix.piProd B = Matrix.piProd (fun i => A i * B i) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.piProd, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => A i (x i) j * B i j (y i))).symm

/-- Adjoint factors coordinatewise for the finite tensor matrix. -/
lemma piProd_adjoint (A : a → Matrix d d ℂ) :
    (Matrix.piProd A).conjTranspose = Matrix.piProd (fun i => (A i).conjTranspose) := by
  ext x y
  simp [Matrix.piProd, Matrix.conjTranspose_apply]

/-- The tensor product of identity matrices is the identity on the Pi basis. -/
lemma piProd_one : Matrix.piProd (fun _ : a => (1 : Matrix d d ℂ)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [Matrix.piProd]
  · have he : ∃ i, x i ≠ y i := by simpa only [funext_iff, not_forall] using h
    obtain ⟨i, hi⟩ := he
    simp only [Matrix.piProd, Matrix.of_apply, Matrix.one_apply, if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The explicit tensor tuple indexed by one generator choice per coordinate. -/
def tuple {m : ℕ} (T : Fin m → Matrix d d ℂ) (I : a → Fin m) :
    Matrix (a → d) (a → d) ℂ := Matrix.piProd (fun i => T (I i))

/-- Every member of the actual tensor tuple is unitary. -/
lemma tuple_unitary {m : ℕ} (T : Fin m → Matrix d d ℂ)
    (hT : ∀ i, (T i).conjTranspose * T i = 1) (I : a → Fin m) :
    (tuple T I).conjTranspose * tuple T I = 1 := by
  rw [tuple, piProd_adjoint, piProd_mul]
  simp_rw [hT]
  exact piProd_one

/-- A generator acts in one input coordinate and as identity elsewhere. -/
def coordinateUnitary {m : ℕ} (T : Fin m → Matrix d d ℂ) (i : a) (j : Fin m) :
    Matrix (a → d) (a → d) ℂ :=
  Matrix.piProd (fun b => if b = i then T j else 1)

/-- The actual coordinate generators are unitary. -/
lemma coordinateUnitary_unitary {m : ℕ} (T : Fin m → Matrix d d ℂ)
    (hT : ∀ j, (T j).conjTranspose * T j = 1) (i : a) (j : Fin m) :
    (coordinateUnitary T i j).conjTranspose * coordinateUnitary T i j = 1 := by
  rw [coordinateUnitary, piProd_adjoint, piProd_mul]
  have h (b : a) :
      (if b = i then T j else 1).conjTranspose * (if b = i then T j else 1) = 1 := by
    split_ifs <;> simp [hT]
  simp_rw [h]
  exact piProd_one

/-- Matching spectators cancel for arbitrary many coordinates. -/
lemma tuple_coordinate_cancellation {m : ℕ} (T : Fin m → Matrix d d ℂ)
    (hT : ∀ j, (T j).conjTranspose * T j = 1)
    (i : a) (I J : a → Fin m) (hIJ : ∀ b, b ≠ i → I b = J b) :
    (tuple T J).conjTranspose * tuple T I =
      (coordinateUnitary T i (J i)).conjTranspose * coordinateUnitary T i (I i) := by
  simp only [tuple, coordinateUnitary, piProd_adjoint, piProd_mul]
  congr 1
  funext b
  by_cases hb : b = i
  · subst b
    simp
  · simp [hb, hIJ b hb, hT]

/-- Cancellation commutes with an arbitrary global sandwich by the suppressor. -/
lemma global_suppressor_coordinate_cancellation {m : ℕ}
    (T : Fin m → Matrix d d ℂ) (hT : ∀ j, (T j).conjTranspose * T j = 1)
    (i : a) (I J : a → Fin m) (hIJ : ∀ b, b ≠ i → I b = J b)
    (H : Matrix (a → d) (a → d) ℂ) :
    H * (tuple T J).conjTranspose * tuple T I * H =
      H * (coordinateUnitary T i (J i)).conjTranspose * coordinateUnitary T i (I i) * H := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ _ H, tuple_coordinate_cancellation T hT i I J hIJ]
  simp only [Matrix.mul_assoc]

/-- Insert the retained coordinate into a tuple of spectator indices. -/
def splitIndex {m : ℕ} (i : a) (j : Fin m) (K : {b : a // b ≠ i} → Fin m) :
    a → Fin m := (Equiv.funSplitAt i (Fin m)).symm (j, K)

lemma splitIndex_at {m : ℕ} (i : a) (j : Fin m)
    (K : {b : a // b ≠ i} → Fin m) : splitIndex i j K i = j := by
  simp [splitIndex, Equiv.funSplitAt, Equiv.piSplitAt]

lemma splitIndex_other {m : ℕ} (i b : a) (hb : b ≠ i) (j : Fin m)
    (K : {b : a // b ≠ i} → Fin m) : splitIndex i j K b = K ⟨b, hb⟩ := by
  simp [splitIndex, Equiv.funSplitAt, Equiv.piSplitAt, hb]

lemma splitIndex_eq_iff {m : ℕ} (i : a) (j j' : Fin m)
    (K : {b : a // b ≠ i} → Fin m) : splitIndex i j K = splitIndex i j' K ↔ j = j' := by
  simp [splitIndex]

/-- The genuine matrix partial trace retaining a prescribed output coordinate. -/
def coordinatePartialTrace {m : ℕ} (i : a)
    (Y : Matrix (a → Fin m) (a → Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (Y.submatrix (Equiv.funSplitAt i (Fin m)).symm
    (Equiv.funSplitAt i (Fin m)).symm).traceRight

/-- For the actual arbitrary-coordinate tensor tuple, summing the spectators
gives exactly the same filtered channel with only the retained generators. -/
lemma coordinate_partial_trace_formula {m : ℕ} (hm : 0 < m)
    (T : Fin m → Matrix d d ℂ) (hT : ∀ j, (T j).conjTranspose * T j = 1)
    (H X : Matrix (a → d) (a → d) ℂ)
    (Y : Matrix (a → Fin m) (a → Fin m) ℂ)
    (hY : ∀ I J, Y I J =
      Matrix.trace ((H * (tuple T J).conjTranspose * tuple T I * H +
        if J = I then 1 - H * H else 0) * X) /
        (Fintype.card (a → Fin m) : ℂ))
    (i : a) (j j' : Fin m) :
    coordinatePartialTrace i Y j j' =
      Matrix.trace ((H * (coordinateUnitary T i j').conjTranspose *
          coordinateUnitary T i j * H + if j' = j then 1 - H * H else 0) * X) /
        (m : ℂ) := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  change (∑ K : {b : a // b ≠ i} → Fin m,
    Y (splitIndex i j K) (splitIndex i j' K)) = _
  have hc (K : {b : a // b ≠ i} → Fin m) :=
    global_suppressor_coordinate_cancellation T hT i
      (splitIndex i j K) (splitIndex i j' K)
      (fun b hb => by rw [splitIndex_other i b hb, splitIndex_other i b hb]) H
  simp only [splitIndex_at] at hc
  simp_rw [hY, hc, splitIndex_eq_iff]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card (a → Fin m) =
      m * Fintype.card ({b : a // b ≠ i} → Fin m) := by
    simpa using Fintype.card_congr (Equiv.funSplitAt i (Fin m))
  rw [hcard, Nat.cast_mul]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hq0 : (Fintype.card ({b : a // b ≠ i} → Fin m) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The same actual partial-trace identity on any finite input space. The
locality hypothesis is a coefficient identity, satisfied by the tensor tuple
through `tuple_coordinate_cancellation` and preserved under a basis relabel. -/
lemma coordinate_partial_trace_of_cancellation {e : Type*}
    [Fintype e] [DecidableEq e] {m : ℕ} (hm : 0 < m)
    (U : (a → Fin m) → Matrix e e ℂ)
    (V : a → Fin m → Matrix e e ℂ)
    (hlocal : ∀ i I J, (∀ b, b ≠ i → I b = J b) →
      (U J).conjTranspose * U I = (V i (J i)).conjTranspose * V i (I i))
    (H X : Matrix e e ℂ) (Y : Matrix (a → Fin m) (a → Fin m) ℂ)
    (hY : ∀ I J, Y I J =
      Matrix.trace ((H * (U J).conjTranspose * U I * H +
        if J = I then 1 - H * H else 0) * X) /
        (Fintype.card (a → Fin m) : ℂ))
    (i : a) (j j' : Fin m) :
    coordinatePartialTrace i Y j j' =
      Matrix.trace ((H * (V i j').conjTranspose * V i j * H +
        if j' = j then 1 - H * H else 0) * X) / (m : ℂ) := by
  classical
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  change (∑ K : {b : a // b ≠ i} → Fin m,
    Y (splitIndex i j K) (splitIndex i j' K)) = _
  have hc (K : {b : a // b ≠ i} → Fin m) :
      H * (U (splitIndex i j' K)).conjTranspose * U (splitIndex i j K) * H =
        H * (V i j').conjTranspose * V i j * H := by
    have h := hlocal i (splitIndex i j K) (splitIndex i j' K)
      (fun b hb => by rw [splitIndex_other i b hb, splitIndex_other i b hb])
    simp only [splitIndex_at] at h
    calc
      _ = H * ((U (splitIndex i j' K)).conjTranspose * U (splitIndex i j K)) * H := by
        simp only [Matrix.mul_assoc]
      _ = H * ((V i j').conjTranspose * V i j) * H := by rw [h]
      _ = _ := by simp only [Matrix.mul_assoc]
  simp_rw [hY, hc, splitIndex_eq_iff]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card (a → Fin m) =
      m * Fintype.card ({b : a // b ≠ i} → Fin m) := by
    simpa using Fintype.card_congr (Equiv.funSplitAt i (Fin m))
  rw [hcard, Nat.cast_mul]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hq0 : (Fintype.card ({b : a // b ≠ i} → Fin m) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

#print axioms tuple_unitary
#print axioms coordinateUnitary_unitary
#print axioms tuple_coordinate_cancellation
#print axioms global_suppressor_coordinate_cancellation
#print axioms coordinate_partial_trace_formula
#print axioms coordinate_partial_trace_of_cancellation

end ActualTensorTuple
