import AdderTrace
import ActualTensorBasis

/-! Exact identification of the circuit permutation tuple with the tensor tuple
used in the entropy estimates. The input labels are enumerated by their cardinality. -/

noncomputable section
open scoped BigOperators

namespace MainAdderTuple

/-- One pair of computational registers. -/
abbrev Register (Q : ℕ) := ZMod Q × ZMod Q

/-- The matrix of the prescribed conjugated adder on one register pair. -/
def generator (Q M : ℕ) [NeZero Q] (i : Fin M) :
    Matrix (Register Q) (Register Q) ℂ :=
  AdderTrace.permutationMatrix (AdderTrace.modularStepPerm Q i.val 1)

lemma generator_unitary (Q M : ℕ) [NeZero Q] (i : Fin M) :
    (generator Q M i).conjTranspose * generator Q M i = 1 := by
  simp only [generator, AdderTrace.permutationMatrix_conjTranspose,
    ← AdderTrace.permutationMatrix_mul, inv_mul_cancel,
    AdderTrace.permutationMatrix_one]

lemma generator_real (Q M : ℕ) [NeZero Q] (i : Fin M) :
    (generator Q M i).map star = generator Q M i := by
  ext x y
  simp [generator, AdderTrace.permutationMatrix, Matrix.map_apply]

lemma generator_circuit (Q M : ℕ) [NeZero Q] (i : Fin M) :
    generator Q M i = AdderTrace.permutationMatrix
      ((AdderTrace.addBtoA Q) ^ i.val * AdderTrace.addAtoB Q *
        ((AdderTrace.addBtoA Q) ^ i.val)⁻¹) := by
  rw [generator, AdderTrace.modularStepPerm_circuit]

lemma tensorAdderMatrix_eq_tuple (Q M r : ℕ) [NeZero Q]
    (I : Fin r → Fin M) :
    AdderTrace.tensorAdderMatrix Q I = ActualTensorTuple.tuple (generator Q M) I := by
  classical
  ext x y
  change (if x = AdderTrace.tensorAdder Q I y then (1 : ℂ) else 0) =
    ∏ a : Fin r, if x a = AdderTrace.modularStepPerm Q (I a).val 1 (y a) then 1 else 0
  by_cases h : x = AdderTrace.tensorAdder Q I y
  · subst x
    simp [AdderTrace.tensorAdder_apply]
  · rw [if_neg h]
    obtain ⟨a, ha⟩ : ∃ a, x a ≠ AdderTrace.tensorAdder Q I y a := by
      simpa only [funext_iff, not_forall] using h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [← AdderTrace.tensorAdder_apply]
    exact if_neg ha

/-- The physical input dimension is precisely Q^(2r). -/
def inputEquiv (Q r : ℕ) [NeZero Q] :
    Fin (Q ^ (2 * r)) ≃ (Fin r → Register Q) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin]
    exact (AdderTrace.tensorLabel_card Q r).symm)

lemma output_enumeration (M r : ℕ) :
    ActualTensorBasis.eOut M r = (AdderTrace.indexEquiv r M).symm := by
  rfl

/-- Both constructions use the identical tensor unitaries after input relabeling. -/
lemma enumeratedTuple_eq_finAdderMatrix (Q M r : ℕ) [NeZero Q]
    (i : Fin (M ^ r)) :
    ActualTensorBasis.enumeratedTuple (inputEquiv Q r) (generator Q M) i =
      (AdderTrace.finAdderMatrix Q r M i).submatrix (inputEquiv Q r) (inputEquiv Q r) := by
  rw [ActualTensorBasis.enumeratedTuple, ActualTensorBasis.reindexedTuple,
    output_enumeration, ← tensorAdderMatrix_eq_tuple]
  rfl

#print axioms tensorAdderMatrix_eq_tuple
#print axioms enumeratedTuple_eq_finAdderMatrix

end MainAdderTuple
