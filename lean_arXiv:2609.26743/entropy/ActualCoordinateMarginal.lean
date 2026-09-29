import ActualTensorTuple

/-!
# A. Actual coordinate marginals and tensor-channel naturality

The recursively defined state marginal is identified with the direct partial
trace obtained by separating an arbitrary coordinate. All marginal identities
are proved from the matrix definitions.
-/

noncomputable section
open scoped BigOperators
open SuppressorEntropy.TensorMarginal

namespace ActualCoordinateMarginal

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The recursive state marginal is exactly the sum over matching spectator
indices, expressed without choosing an enumeration of those spectators. -/
lemma coordinateMarginal_entry {r : ℕ} (ρ : MState (Fin r → α))
    (a : Fin r) (i j : α) :
    (coordinateMarginal ρ a).m i j =
      ∑ f : Fin r → α, if f a = i then ρ.m f (Function.update f a j) else 0 := by
  induction r with
  | zero => exact Fin.elim0 a
  | succ r ih =>
    refine Fin.cases ?_ (fun a => ?_) a
    · change (∑ f : Fin r → α, ρ.m (Fin.cons i f) (Fin.cons j f)) = _
      have hsum := (headTailEquiv α r).sum_comp
        (fun f : Fin (r+1) → α => if f 0 = i then ρ.m f (Function.update f 0 j) else 0)
      rw [← hsum]
      simp [headTailEquiv, Fintype.sum_prod_type, Fin.update_cons_zero]
    · change (coordinateMarginal (ρ.relabel (headTailEquiv α r)).traceLeft a).m i j = _
      rw [ih]
      change (∑ f : Fin r → α, if f a = i then
        (∑ b : α, ρ.m (Fin.cons b f) (Fin.cons b (Function.update f a j))) else 0) = _
      have hsum := (headTailEquiv α r).sum_comp
        (fun f : Fin (r+1) → α => if f a.succ = i then
          ρ.m f (Function.update f a.succ j) else 0)
      rw [← hsum]
      simp only [headTailEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
        Fin.cons_succ, ← Fin.cons_update]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      split_ifs <;> simp

omit [Fintype α] [DecidableEq α] in
lemma split_at {r : ℕ} (a : Fin r) (i : α)
    (f : {b : Fin r // b ≠ a} → α) :
    (Equiv.funSplitAt a α).symm (i,f) a = i := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype α] [DecidableEq α] in
lemma split_update {r : ℕ} (a : Fin r) (i j : α)
    (f : {b : Fin r // b ≠ a} → α) :
    Function.update ((Equiv.funSplitAt a α).symm (i,f)) a j =
      (Equiv.funSplitAt a α).symm (j,f) := by
  funext b
  by_cases hb : b = a
  · subst b
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Function.update, hb, Equiv.funSplitAt, Equiv.piSplitAt]

/-- The direct coordinate partial trace has the same spectator-sum formula. -/
lemma split_partial_trace_entry {r : ℕ}
    (X : Matrix (Fin r → α) (Fin r → α) ℂ) (a : Fin r) (i j : α) :
    (X.submatrix (Equiv.funSplitAt a α).symm
      (Equiv.funSplitAt a α).symm).traceRight i j =
      ∑ f : Fin r → α, if f a = i then X f (Function.update f a j) else 0 := by
  change (∑ f : {b : Fin r // b ≠ a} → α,
    X ((Equiv.funSplitAt a α).symm (i,f)) ((Equiv.funSplitAt a α).symm (j,f))) = _
  have hsum := (Equiv.funSplitAt a α).symm.sum_comp
    (fun f : Fin r → α => if f a = i then X f (Function.update f a j) else 0)
  rw [← hsum, Fintype.sum_prod_type]
  simp_rw [split_at, split_update]
  simp

/-- The existing recursive state marginal equals the actual partial trace
after splitting off the selected coordinate. -/
lemma coordinateMarginal_eq_split {r : ℕ} (ρ : MState (Fin r → α)) (a : Fin r) :
    coordinateMarginal ρ a = (ρ.relabel (Equiv.funSplitAt a α).symm).traceRight := by
  apply MState.ext_m
  ext i j
  rw [coordinateMarginal_entry]
  exact (split_partial_trace_entry ρ.m a i j).symm

/-- Identification with the matrix partial trace used for the actual tensor
tuple cancellation theorem. -/
lemma coordinateMarginal_matrix {m r : ℕ} (ρ : MState (Fin r → Fin m)) (a : Fin r) :
    (coordinateMarginal ρ a).m = ActualTensorTuple.coordinatePartialTrace a ρ.m := by
  rw [coordinateMarginal_eq_split]
  rfl

/-- The actual CPTP map discarding every output coordinate except `a`. -/
def coordinateTraceChannel {r : ℕ} (a : Fin r) : CPTPMap (Fin r → α) α :=
  CPTPMap.traceRight.compose (CPTPMap.ofEquiv (Equiv.funSplitAt a α))

lemma coordinateTraceChannel_map {r : ℕ} (a : Fin r)
    (X : Matrix (Fin r → α) (Fin r → α) ℂ) (i j : α) :
    (coordinateTraceChannel (α := α) a).map X i j =
      ∑ f : {b : Fin r // b ≠ a} → α,
        X ((Equiv.funSplitAt a α).symm (i,f)) ((Equiv.funSplitAt a α).symm (j,f)) := rfl

/-- The coordinate CPTP map acts as the existing recursive state marginal. -/
lemma coordinateTraceChannel_apply {r : ℕ} (a : Fin r) (ρ : MState (Fin r → α)) :
    coordinateTraceChannel (α := α) a ρ = coordinateMarginal ρ a := by
  rw [coordinateMarginal_eq_split]
  simp [coordinateTraceChannel, CPTPMap.compose_eq]

omit [Fintype α] [DecidableEq α] in
lemma pair_split_index {r : ℕ} (a : Fin r) (i j : α)
    (f : {b : Fin r // b ≠ a} → α × α) :
    pairCoordinatesEquiv α r ((Equiv.funSplitAt a (α × α)).symm ((i,j),f)) =
      ((Equiv.funSplitAt a α).symm (i,fun b => (f b).1),
       (Equiv.funSplitAt a α).symm (j,fun b => (f b).2)) := by
  apply Prod.ext <;> funext b <;> by_cases hb : b = a
  all_goals simp [pairCoordinatesEquiv, Equiv.funSplitAt, Equiv.piSplitAt, hb]

/-- The genuine paired-coordinate state has independent spectator sums in
the two copies. -/
lemma paired_coordinate_entry {r : ℕ}
    (Y : MState ((Fin r → α) × (Fin r → α))) (a : Fin r) (i j i' j' : α) :
    (coordinateMarginal (Y.relabel (pairCoordinatesEquiv α r)) a).m (i,j) (i',j') =
      ∑ f : {b : Fin r // b ≠ a} → α, ∑ g : {b : Fin r // b ≠ a} → α,
        Y.m (((Equiv.funSplitAt a α).symm (i,f)), ((Equiv.funSplitAt a α).symm (j,g)))
          (((Equiv.funSplitAt a α).symm (i',f)), ((Equiv.funSplitAt a α).symm (j',g))) := by
  rw [coordinateMarginal_eq_split]
  change (∑ f : {b : Fin r // b ≠ a} → α × α,
    Y.m (pairCoordinatesEquiv α r ((Equiv.funSplitAt a (α × α)).symm ((i,j),f)))
      (pairCoordinatesEquiv α r ((Equiv.funSplitAt a (α × α)).symm ((i',j'),f)))) = _
  simp_rw [pair_split_index]
  let e := Equiv.arrowProdEquivProdArrow {b : Fin r // b ≠ a}
    (fun _ => α) (fun _ => α)
  have hsum := e.symm.sum_comp (fun f : {b : Fin r // b ≠ a} → α × α =>
    Y.m ((Equiv.funSplitAt a α).symm (i,fun b => (f b).1),
        (Equiv.funSplitAt a α).symm (j,fun b => (f b).2))
      ((Equiv.funSplitAt a α).symm (i',fun b => (f b).1),
        (Equiv.funSplitAt a α).symm (j',fun b => (f b).2)))
  rw [← hsum, Fintype.sum_prod_type]
  rfl

set_option maxRecDepth 2000 in
/-- Tracing spectators independently in both outputs equals the actual
coordinate-pair marginal after regrouping. -/
lemma paired_coordinate_trace {r : ℕ}
    (Y : MState ((Fin r → α) × (Fin r → α))) (a : Fin r) :
    ((coordinateTraceChannel (α := α) a).prod (coordinateTraceChannel (α := α) a)) Y =
      coordinateMarginal (Y.relabel (pairCoordinatesEquiv α r)) a := by
  apply MState.ext_m
  ext ⟨i,j⟩ ⟨i',j'⟩
  rw [paired_coordinate_entry]
  change ((coordinateTraceChannel (α := α) a).map.kron (coordinateTraceChannel (α := α) a).map)
    Y.m (i,j) (i',j') = _
  rw [MatrixMap.kron_def]
  simp_rw [coordinateTraceChannel_map]
  simp only [Matrix.single, Matrix.of_apply, ite_and, Finset.mul_sum, Finset.sum_mul,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]
  conv_lhs =>
    enter [2, x, 2, x', 2, y]
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs =>
    enter [2, x, 2, x']
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs =>
    enter [2, x]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, g, 2, x]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, g]
    rw [Finset.sum_comm]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

set_option maxRecDepth 2000 in
/-- Actual paired-channel naturality for every tensor coordinate and every
joint input. No marginal identity is assumed. -/
lemma paired_channel_coordinate_marginal {r : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Φ Ψ : CPTPMap ι (Fin r → α)) (X : MState (ι × ι)) (a : Fin r) :
    coordinateMarginal (((Φ.prod Ψ) X).relabel (pairCoordinatesEquiv α r)) a =
      (((coordinateTraceChannel (α := α) a).compose Φ).prod
        ((coordinateTraceChannel (α := α) a).compose Ψ)) X := by
  have hcomp :
      ((coordinateTraceChannel (α := α) a).compose Φ).prod ((coordinateTraceChannel (α := α) a).compose Ψ) =
      ((coordinateTraceChannel (α := α) a).prod (coordinateTraceChannel (α := α) a)).compose (Φ.prod Ψ) := by
    apply CPTPMap.ext
    exact MatrixMap.kron_comp_distrib Φ.map _ Ψ.map _
  rw [hcomp, CPTPMap.compose_eq, paired_coordinate_trace]

#print axioms coordinateMarginal_entry
#print axioms coordinateMarginal_eq_split
#print axioms coordinateMarginal_matrix
#print axioms paired_coordinate_trace
#print axioms paired_channel_coordinate_marginal

end ActualCoordinateMarginal
