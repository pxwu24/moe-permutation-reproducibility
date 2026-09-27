import ActualTensorTuple
import Mathlib.Data.Fintype.EquivFin

/-!
# A. Finite basis labels for the actual tensor construction

These definitions put the tensor input on `Fin n` and enumerate the output
tuples by `Fin (M^r)`. Unitarity, coordinate cancellation, and entrywise
reality are all preserved by these actual basis reindexings.
-/

noncomputable section
open scoped BigOperators Kronecker

namespace ActualTensorBasis

variable {d : Type*} [Fintype d] [DecidableEq d] {n M r : ℕ}

/-- The actual tensor tuple expressed in a prescribed finite input basis. -/
def reindexedTuple (e : Fin n ≃ (Fin r → d)) (T : Fin M → Matrix d d ℂ)
    (I : Fin r → Fin M) : Matrix (Fin n) (Fin n) ℂ :=
  (ActualTensorTuple.tuple T I).submatrix e e

/-- A single-coordinate generator in the same finite input basis. -/
def reindexedCoordinate (e : Fin n ≃ (Fin r → d)) (T : Fin M → Matrix d d ℂ)
    (a : Fin r) (i : Fin M) : Matrix (Fin n) (Fin n) ℂ :=
  (ActualTensorTuple.coordinateUnitary T a i).submatrix e e

/-- Every reindexed tensor matrix is unitary. -/
lemma reindexedTuple_unitary (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).conjTranspose * T i = 1)
    (I : Fin r → Fin M) :
    (reindexedTuple e T I).conjTranspose * reindexedTuple e T I = 1 := by
  rw [reindexedTuple, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    ActualTensorTuple.tuple_unitary T hT, Matrix.submatrix_one_equiv]

/-- Every reindexed coordinate generator is unitary. -/
lemma reindexedCoordinate_unitary (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).conjTranspose * T i = 1)
    (a : Fin r) (i : Fin M) :
    (reindexedCoordinate e T a i).conjTranspose * reindexedCoordinate e T a i = 1 := by
  rw [reindexedCoordinate, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    ActualTensorTuple.coordinateUnitary_unitary T hT, Matrix.submatrix_one_equiv]

/-- Spectator cancellation survives the actual input-basis reindexing. -/
lemma reindexed_coordinate_cancellation (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).conjTranspose * T i = 1)
    (a : Fin r) (I J : Fin r → Fin M) (hIJ : ∀ b, b ≠ a → I b = J b) :
    (reindexedTuple e T J).conjTranspose * reindexedTuple e T I =
      (reindexedCoordinate e T a (J a)).conjTranspose * reindexedCoordinate e T a (I a) := by
  simp only [reindexedTuple, reindexedCoordinate, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  rw [ActualTensorTuple.tuple_coordinate_cancellation T hT a I J hIJ]

omit [Fintype d] [DecidableEq d] in
/-- Entrywise conjugation fixes a tensor product of real matrices. -/
lemma piProd_real (A : Fin r → Matrix d d ℂ) (hA : ∀ a, (A a).map star = A a) :
    (Matrix.piProd A).map star = Matrix.piProd A := by
  ext x y
  change (starRingEnd ℂ) (∏ a, A a (x a) (y a)) = ∏ a, A a (x a) (y a)
  rw [map_prod]
  exact Finset.prod_congr rfl fun a _ => congrFun (congrFun (hA a) (x a)) (y a)

omit [Fintype d] [DecidableEq d] in
/-- The original tensor tuple is real whenever its prescribed factors are real. -/
lemma tuple_real (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).map star = T i)
    (I : Fin r → Fin M) :
    (ActualTensorTuple.tuple T I).map star = ActualTensorTuple.tuple T I :=
  piProd_real (fun a => T (I a)) (fun a => hT (I a))

omit [Fintype d] in
/-- A single-coordinate tensor generator is real for real prescribed factors. -/
lemma coordinate_real (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).map star = T i)
    (a : Fin r) (i : Fin M) :
    (ActualTensorTuple.coordinateUnitary T a i).map star =
      ActualTensorTuple.coordinateUnitary T a i := by
  apply piProd_real
  intro b
  split_ifs
  · exact hT i
  · ext x y
    simp [Matrix.map_apply, Matrix.one_apply]

omit [Fintype d] [DecidableEq d] in
/-- The input-basis reindexing preserves reality of every tensor matrix. -/
lemma reindexedTuple_real (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).map star = T i)
    (I : Fin r → Fin M) :
    (reindexedTuple e T I).map star = reindexedTuple e T I := by
  rw [reindexedTuple, ← Matrix.submatrix_map, tuple_real T hT]

omit [Fintype d] in
/-- The input-basis reindexing preserves reality of every coordinate generator. -/
lemma reindexedCoordinate_real (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).map star = T i)
    (a : Fin r) (i : Fin M) :
    (reindexedCoordinate e T a i).map star = reindexedCoordinate e T a i := by
  rw [reindexedCoordinate, ← Matrix.submatrix_map, coordinate_real T hT]

/-- Enumerate all `M^r` output tuples by their finite cardinality. -/
def eOut (M r : ℕ) : Fin (M ^ r) ≃ (Fin r → Fin M) :=
  Fintype.equivOfCardEq (by simp)

/-- A finite input basis with the exact tensor-product cardinality. -/
def eInput (d : Type*) [Fintype d] (r : ℕ) :
    Fin (Fintype.card d ^ r) ≃ (Fin r → d) :=
  Fintype.equivOfCardEq (by simp)

/-- The actual tensor tuple with both input and output finite labels. -/
def enumeratedTuple (e : Fin n ≃ (Fin r → d)) (T : Fin M → Matrix d d ℂ)
    (I : Fin (M ^ r)) : Matrix (Fin n) (Fin n) ℂ :=
  reindexedTuple e T (eOut M r I)

/-- Output enumeration preserves the original unitary identities. -/
lemma enumeratedTuple_unitary (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).conjTranspose * T i = 1)
    (I : Fin (M ^ r)) :
    (enumeratedTuple e T I).conjTranspose * enumeratedTuple e T I = 1 :=
  reindexedTuple_unitary e T hT _

/-- Both unitary identities hold for the enumerated tensor tuple. -/
lemma enumeratedTuple_unitary_right (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).conjTranspose * T i = 1)
    (I : Fin (M ^ r)) :
    enumeratedTuple e T I * (enumeratedTuple e T I).conjTranspose = 1 := by
  exact mul_eq_one_comm.mp (enumeratedTuple_unitary e T hT I)

omit [Fintype d] [DecidableEq d] in
/-- Output enumeration preserves entrywise reality. -/
lemma enumeratedTuple_real (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).map star = T i)
    (I : Fin (M ^ r)) :
    (enumeratedTuple e T I).map star = enumeratedTuple e T I :=
  reindexedTuple_real e T hT _

/-- Cancellation for numerically indexed outputs, expressed by their coordinates. -/
lemma enumerated_coordinate_cancellation (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).conjTranspose * T i = 1)
    (a : Fin r) (I J : Fin (M ^ r))
    (hIJ : ∀ b, b ≠ a → eOut M r I b = eOut M r J b) :
    (enumeratedTuple e T J).conjTranspose * enumeratedTuple e T I =
      (reindexedCoordinate e T a (eOut M r J a)).conjTranspose *
        reindexedCoordinate e T a (eOut M r I a) :=
  reindexed_coordinate_cancellation e T hT a _ _ hIJ

omit [Fintype d] [DecidableEq d] in
/-- Recover the Pi-indexed tensor matrix from its output enumeration. -/
lemma enumeratedTuple_output_inverse (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (I : Fin r → Fin M) :
    enumeratedTuple e T ((eOut M r).symm I) = reindexedTuple e T I := by
  simp only [enumeratedTuple, Equiv.apply_symm_apply]

#print axioms reindexedTuple_unitary
#print axioms reindexedCoordinate_unitary
#print axioms reindexed_coordinate_cancellation
#print axioms piProd_real
#print axioms reindexedTuple_real
#print axioms reindexedCoordinate_real
#print axioms enumeratedTuple_unitary
#print axioms enumeratedTuple_unitary_right
#print axioms enumeratedTuple_real
#print axioms enumerated_coordinate_cancellation
#print axioms enumeratedTuple_output_inverse

end ActualTensorBasis
