import MainHolevo

/-!
# Entropy of the flagged Weyl extension

Arbitrary flagged input states, including states entangled with the flag,
produce convex combinations of unitary conjugates of outputs of the original
channel. The weights and normalized conditional states are constructed from
the positive diagonal input blocks.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators RealInnerProductSpace ComplexOrder
open MainHolevo

namespace MainFlaggedEntropy

variable {n d ι : Type} [Fintype n] [Fintype d] [Fintype ι]
variable [DecidableEq n] [DecidableEq d] [DecidableEq ι]

def inputBlock (ρ : MState (n × ι)) (i : ι) : HermitianMat n ℂ :=
  ⟨ρ.m.submatrix (fun x ↦ (x,i)) (fun x ↦ (x,i)),
    ρ.M.H.submatrix (fun x ↦ (x,i))⟩

theorem inputBlock_nonneg (ρ : MState (n × ι)) (i : ι) :
    0 ≤ inputBlock ρ i :=
  HermitianMat.zero_le_iff.mpr (ρ.psd.submatrix (fun x ↦ (x,i)))

theorem inputBlock_trace_nonneg (ρ : MState (n × ι)) (i : ι) :
    0 ≤ (inputBlock ρ i).trace :=
  HermitianMat.trace_nonneg (inputBlock_nonneg ρ i)

theorem sum_inputBlock_trace (ρ : MState (n × ι)) :
    ∑ i, (inputBlock ρ i).trace = 1 := by
  rw [← ρ.tr]
  simp_rw [HermitianMat.trace_eq_re_trace]
  simp only [inputBlock, Matrix.trace,
    Matrix.diag_apply, Matrix.submatrix_apply, map_sum, Fintype.sum_prod_type]
  change (∑ i : ι, ∑ x : n, (ρ.m (x,i) (x,i)).re) =
    ∑ x : n, ∑ i : ι, (ρ.m (x,i) (x,i)).re
  rw [Finset.sum_comm]

def blockDistribution (ρ : MState (n × ι)) : ProbDistribution ι :=
  ProbDistribution.mk' (fun i ↦ (inputBlock ρ i).trace)
    (inputBlock_trace_nonneg ρ) (sum_inputBlock_trace ρ)

@[simp] theorem blockDistribution_apply (ρ : MState (n × ι)) (i : ι) :
    (blockDistribution ρ i : ℝ) = (inputBlock ρ i).trace := rfl

theorem block_eq_zero_of_trace_zero (ρ : MState (n × ι)) (i : ι)
    (h : (inputBlock ρ i).trace = 0) : inputBlock ρ i = 0 := by
  by_contra hne
  have hp := HermitianMat.trace_pos
    (lt_of_le_of_ne (inputBlock_nonneg ρ i) (Ne.symm hne))
  linarith

def normalizedBlock [Nonempty n] (ρ : MState (n × ι)) (i : ι) : MState n :=
  if h : 0 < (inputBlock ρ i).trace then
    { M := (inputBlock ρ i).trace⁻¹ • inputBlock ρ i
      nonneg := smul_nonneg (inv_nonneg.mpr h.le) (inputBlock_nonneg ρ i)
      tr := by simp [HermitianMat.trace_smul, h.ne'] }
  else MState.uniform

theorem weighted_normalizedBlock [Nonempty n] (ρ : MState (n × ι)) (i : ι) :
    (blockDistribution ρ i : ℝ) • (normalizedBlock ρ i).M = inputBlock ρ i := by
  rw [blockDistribution_apply]
  unfold normalizedBlock
  split_ifs with h
  · simp [smul_smul, h.ne']
  · have hz : (inputBlock ρ i).trace = 0 :=
      le_antisymm (le_of_not_gt h) (inputBlock_trace_nonneg ρ i)
    simp [hz, block_eq_zero_of_trace_zero ρ i hz]

theorem matrixMap_apply_entry (Φ : CPTPMap n d) (X : Matrix n n ℂ) (a b : d) :
    Φ.map X a b = ∑ x, ∑ y, X x y * Φ.map (Matrix.single x y 1) a b := by
  have h := congrArg (fun T : MatrixMap n d ℂ ↦ T X a b)
    (MatrixMap.choi_map_inv Φ.map)
  exact h.symm

theorem prod_id_block (Φ : CPTPMap n d) (ρ : MState (n × ι))
    (a b : d) (i : ι) :
    ((Φ ⊗ᶜᵖ (CPTPMap.id : CPTPMap ι ι)) ρ).m (a,i) (b,i) =
      Φ.map (inputBlock ρ i).mat a b := by
  change (Φ.map.kron (CPTPMap.id : CPTPMap ι ι).map) ρ.m (a,i) (b,i) = _
  rw [MatrixMap.kron_def, matrixMap_apply_entry]
  simp [CPTPMap.id_map, Matrix.single, ite_and, inputBlock, mul_comm]
  rfl

theorem flaggedExtension_entry (Φ : CPTPMap n d)
    (U : ι → Matrix.unitaryGroup d ℂ) (ρ : MState (n × ι)) (a b : d) :
    (flaggedExtension Φ U ρ).m a b =
      ∑ i, ∑ x, ∑ y, (U i).val a x *
        Φ.map (inputBlock ρ i).mat x y * star ((U i).val b y) := by
  simp only [flaggedExtension, CPTPMap.compose_eq, CPTPMap.ofUnitary_eq_conj,
    CPTPMap.traceRight_eq_MState_traceRight]
  change (∑ i, ((((Φ ⊗ᶜᵖ (CPTPMap.id : CPTPMap ι ι)) ρ).M.conj
    (controlledUnitary U).val).mat (a,i) (b,i))) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [controlled_conj_entry]
  simp_rw [MState.mat_M, prod_id_block]

theorem map_inputBlock [Nonempty n] (Φ : CPTPMap n d)
    (ρ : MState (n × ι)) (i : ι) :
    Φ.map (inputBlock ρ i).mat =
      (blockDistribution ρ i : ℝ) • (Φ (normalizedBlock ρ i)).m := by
  rw [← weighted_normalizedBlock ρ i]
  change Φ.map ((blockDistribution ρ i : ℂ) • (normalizedBlock ρ i).m) =
    (blockDistribution ρ i : ℂ) • Φ.map (normalizedBlock ρ i).m
  exact map_smul _ _ _

/-- The output is the actual convex combination of normalized diagonal blocks. -/
theorem flaggedExtension_average [Nonempty n] (Φ : CPTPMap n d)
    (U : ι → Matrix.unitaryGroup d ℂ) (ρ : MState (n × ι)) :
    flaggedExtension Φ U ρ = average (blockDistribution ρ)
      (fun i ↦ (Φ (normalizedBlock ρ i)).uConj (U i)) := by
  apply MState.ext_m
  ext a b
  rw [flaggedExtension_entry]
  change _ = (average (blockDistribution ρ)
    (fun i ↦ (Φ (normalizedBlock ρ i)).uConj (U i))).M.mat a b
  rw [average_M]
  simp only [HermitianMat.mat_finset_sum, Matrix.sum_apply, HermitianMat.mat_smul,
    Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_inputBlock]
  change (∑ x, ∑ y, (U i).val a x *
      ((blockDistribution ρ i : ℂ) * (Φ (normalizedBlock ρ i)).m x y) *
      star ((U i).val b y)) =
    (blockDistribution ρ i : ℂ) *
      ((U i).val * (Φ (normalizedBlock ρ i)).m * (U i).val.conjTranspose) a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- An entropy lower bound for the base channel holds for every input of its
flagged extension, including entangled flagged inputs. -/
theorem flaggedExtension_entropy_lower [Nonempty n] (Φ : CPTPMap n d)
    (U : ι → Matrix.unitaryGroup d ℂ) {h : ℝ}
    (hS : ∀ σ, h ≤ Sᵥₙ (Φ σ)) (ρ : MState (n × ι)) :
    h ≤ Sᵥₙ (flaggedExtension Φ U ρ) := by
  rw [flaggedExtension_average]
  apply le_trans _ (entropy_average_ge _ _)
  calc
    h = ∑ i, (blockDistribution ρ i : ℝ) * h := by
      rw [← Finset.sum_mul, (blockDistribution ρ).normalized, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (by simpa using hS (normalizedBlock ρ i))
        (blockDistribution ρ i).zero_le_coe

/-- The flagged extension preserves minimum output entropy. -/
theorem flaggedExtension_minimumOutputEntropy [Nonempty n] [Nonempty ι]
    (Φ : CPTPMap n d) (U : ι → Matrix.unitaryGroup d ℂ) :
    SuppressorEntropy.minimumOutputEntropy (flaggedExtension Φ U) =
      SuppressorEntropy.minimumOutputEntropy Φ := by
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty _)
    rintro x ⟨σ, rfl⟩
    let i : ι := Classical.choice inferInstance
    have h := SuppressorEntropy.minimumOutputEntropy_le (flaggedExtension Φ U)
      (σ ⊗ᴹ MState.pure (Ket.basis i))
    simpa only [flaggedExtension_basis, entropy_uConj] using h
  · apply le_csInf (Set.range_nonempty _)
    rintro x ⟨ρ, rfl⟩
    exact flaggedExtension_entropy_lower Φ U
      (SuppressorEntropy.minimumOutputEntropy_le Φ) ρ

/-- The one-copy Holevo upper bound transfers to the actual flagged channel. -/
theorem flaggedExtension_holevo_upper [Nonempty n] [Nonempty ι]
    (Φ : CPTPMap n d) (U : ι → Matrix.unitaryGroup d ℂ) {h : ℝ}
    (hS : ∀ σ, h ≤ Sᵥₙ (Φ σ)) :
    holevo (flaggedExtension Φ U) ≤ Real.log (Fintype.card d) - h :=
  holevo_le_of_entropy_lower _ (flaggedExtension_entropy_lower Φ U hS)

end MainFlaggedEntropy

#print axioms MainFlaggedEntropy.flaggedExtension_entropy_lower
#print axioms MainFlaggedEntropy.flaggedExtension_minimumOutputEntropy
