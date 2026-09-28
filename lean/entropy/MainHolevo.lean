import SingleEntropy
import QuantumInfo.Entropy.SSA
import QuantumInfo.ForMathlib.HermitianMat.Peierls

/-!
Finite ensembles, their Holevo information, and the entropy cost of adding a
finite pure ancilla and discarding it after a unitary.  Logarithms are natural.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open ProbDistribution

namespace MainHolevo

variable {n d e ι : Type} [Fintype n] [Fintype d] [Fintype e] [Fintype ι]
variable [DecidableEq n] [DecidableEq d] [DecidableEq e]

/-- The barycentre of a finite ensemble of density matrices. -/
def average (p : ProbDistribution ι) (ρ : ι → MState d) : MState d :=
  expect_val ⟨ρ, p⟩

@[simp] theorem average_M (p : ProbDistribution ι) (ρ : ι → MState d) :
    (average p ρ).M = ∑ i, (p i : ℝ) • (ρ i).M := by
  change Mixable.to_U (expect_val ⟨ρ, p⟩) = _
  simp only [expect_val, Mixable.to_U_of_mkT]
  rfl

/-- Concavity of von Neumann entropy for arbitrary finite mixtures. -/
theorem entropy_average_ge (p : ProbDistribution ι) (ρ : ι → MState d) :
    ∑ i, (p i : ℝ) * Sᵥₙ (ρ i) ≤ Sᵥₙ (average p ρ) := by
  have hc := HermitianMat.trace_function_convex_ici
    (d := d) Real.concaveOn_negMulLog.neg
  have hh := hc.map_sum_le (t := Finset.univ)
    (w := fun i ↦ (p i : ℝ)) (p := fun i ↦ (ρ i).M)
    (fun i _ ↦ (p i).zero_le_coe) p.normalized
    (fun i _ ↦ (ρ i).nonneg)
  simp only [HermitianMat.cfc_neg, HermitianMat.trace_neg,
    ← Sᵥₙ_eq_trace_cfc_negMulLog, smul_eq_mul, mul_neg, Finset.sum_neg_distrib,
    ← average_M p ρ] at hh
  linarith

/-- Holevo information of a specified finite ensemble after a channel. -/
def ensembleHolevo (Φ : MState n → MState d)
    (p : ProbDistribution ι) (ρ : ι → MState n) : ℝ :=
  Sᵥₙ (average p (fun i ↦ Φ (ρ i))) - ∑ i, (p i : ℝ) * Sᵥₙ (Φ (ρ i))

/-- The achievable finite-ensemble Holevo informations. -/
def holevoRange (Φ : MState n → MState d) : Set ℝ :=
  {x | ∃ (ι : Type) (hι : Fintype ι) (p : @ProbDistribution ι hι)
    (ρ : ι → MState n), x = @ensembleHolevo n d ι _ _ hι _ _ Φ p ρ}

/-- One-shot Holevo information, with no capacity theorem built into its definition. -/
def holevo (Φ : MState n → MState d) : ℝ := sSup (holevoRange Φ)

theorem ensembleHolevo_le_of_entropy_lower (Φ : MState n → MState d)
    (p : ProbDistribution ι) (ρ : ι → MState n) {h : ℝ}
    (hS : ∀ σ, h ≤ Sᵥₙ (Φ σ)) :
    ensembleHolevo Φ p ρ ≤ Real.log (Fintype.card d) - h := by
  have hsum : h ≤ ∑ i, (p i : ℝ) * Sᵥₙ (Φ (ρ i)) := by
    calc
      h = ∑ i, (p i : ℝ) * h := by simp [← Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hS _) (p i).zero_le_coe
  have hmax := Sᵥₙ_le_log_d (average p (fun i ↦ Φ (ρ i)))
  unfold ensembleHolevo
  simpa only [Finset.card_univ] using sub_le_sub hmax hsum

theorem holevoRange_bddAbove (Φ : MState n → MState d) :
    BddAbove (holevoRange Φ) := by
  refine ⟨Real.log (Fintype.card d), ?_⟩
  rintro x ⟨ι, hι, p, ρ, rfl⟩
  simpa using ensembleHolevo_le_of_entropy_lower Φ p ρ (fun σ ↦ Sᵥₙ_nonneg (Φ σ))

theorem ensembleHolevo_le_holevo (Φ : MState n → MState d)
    (p : ProbDistribution ι) (ρ : ι → MState n) :
    ensembleHolevo Φ p ρ ≤ holevo Φ := by
  exact le_csSup (holevoRange_bddAbove Φ) ⟨ι, inferInstance, p, ρ, rfl⟩

theorem holevo_le_of_entropy_lower [Nonempty n] (Φ : MState n → MState d)
    {h : ℝ} (hS : ∀ σ, h ≤ Sᵥₙ (Φ σ)) :
    holevo Φ ≤ Real.log (Fintype.card d) - h := by
  apply csSup_le
  · exact ⟨ensembleHolevo Φ (ProbDistribution.constant ()) (fun _ : Unit ↦ MState.uniform),
      Unit, inferInstance, ProbDistribution.constant (), (fun _ ↦ MState.uniform), rfl⟩
  · rintro x ⟨ι, hι, p, ρ, rfl⟩
    exact ensembleHolevo_le_of_entropy_lower Φ p ρ hS

@[simp] theorem entropy_uConj (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) :
    Sᵥₙ (ρ.uConj U) = Sᵥₙ ρ := by simp [Sᵥₙ]

/-- The maximally mixed state has entropy log of its dimension. -/
@[simp] theorem entropy_uniform [Nonempty d] :
    Sᵥₙ (MState.uniform : MState d) = Real.log (Fintype.card d) := by
  rw [Sᵥₙ_eq_trace_cfc_negMulLog]
  change (HermitianMat.cfc (HermitianMat.diagonal ℂ
    (fun i : d ↦ (ProbDistribution.uniform i : ℝ))) Real.negMulLog).trace = _
  rw [HermitianMat.cfc_diagonal, HermitianMat.trace_diagonal]
  simpa only [Hₛ, H₁, ProbDistribution.prob, Finset.card_univ, Function.comp_apply] using
    (Hₛ_uniform (α := d))

/-- A uniformly weighted unitary orbit whose average is maximally mixed achieves
`log d - S(ρ)`.  The hypothesis is an equality of actual density matrices. -/
theorem orbit_ensembleHolevo [Nonempty ι] [Nonempty d]
    (Φ : MState n → MState d) (inputs : ι → MState n)
    (ρ : MState d) (U : ι → Matrix.unitaryGroup d ℂ)
    (houtputs : ∀ i, Φ (inputs i) = ρ.uConj (U i))
    (htwirl : average ProbDistribution.uniform (fun i ↦ ρ.uConj (U i)) = MState.uniform) :
    Real.log (Fintype.card d) - Sᵥₙ ρ ≤ holevo Φ := by
  have heq : ensembleHolevo Φ ProbDistribution.uniform inputs =
      Real.log (Fintype.card d) - Sᵥₙ ρ := by
    unfold ensembleHolevo
    simp_rw [houtputs, entropy_uConj]
    rw [htwirl, entropy_uniform]
    simp [← Finset.sum_mul]
  rw [← heq]
  exact ensembleHolevo_le_holevo Φ _ inputs

/-- Tensoring with a pure state does not change entropy. -/
theorem entropy_pure_prod (ψ : Ket e) (ρ : MState d) :
    Sᵥₙ (MState.pure ψ ⊗ᴹ ρ) = Sᵥₙ ρ := by
  have hup := Sᵥₙ_subadditivity (MState.pure ψ ⊗ᴹ ρ)
  have hlo := Sᵥₙ_triangle_ineq_one_way (MState.pure ψ ⊗ᴹ ρ).SWAP
  simp at hup hlo
  exact le_antisymm hup hlo

/-- Discarding a finite pure ancilla after a unitary costs at most log of its
size.  This is the entropy-of-mixture estimate in a unitary dilation form. -/
theorem entropy_discard_ancilla (ψ : Ket e) (ρ : MState d)
    (U : Matrix.unitaryGroup (e × d) ℂ) :
    Sᵥₙ ((MState.pure ψ ⊗ᴹ ρ).uConj U).traceLeft ≤
      Sᵥₙ ρ + Real.log (Fintype.card e) := by
  let σ := (MState.pure ψ ⊗ᴹ ρ).uConj U
  have h := Sᵥₙ_triangle_ineq_one_way σ.SWAP
  have hb := Sᵥₙ_le_log_d σ.traceRight
  have he : Sᵥₙ σ = Sᵥₙ ρ := by
    simp [σ, entropy_pure_prod]
  simp only [MState.traceRight_SWAP, MState.traceLeft_SWAP, Sᵥₙ_of_SWAP_eq] at h
  simp only [Finset.card_univ] at hb
  linarith

variable [DecidableEq ι]

/-- A unitary controlled by a finite classical register. -/
def controlledUnitary (U : ι → Matrix.unitaryGroup d ℂ) :
    Matrix.unitaryGroup (d × ι) ℂ := by
  refine ⟨Matrix.blockDiagonal (fun i ↦ (U i).val), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.blockDiagonal _ * (Matrix.blockDiagonal _).conjTranspose = 1
  rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have hfun : (fun i ↦ (U i).val * ((U i).val).conjTranspose) = 1 := by
    funext i
    exact Matrix.mem_unitaryGroup_iff.mp (U i).property
  rw [hfun, Matrix.blockDiagonal_one]

/-- The actual flagged-input covariant completion: apply the original channel,
then a controlled output unitary, then discard the flag. -/
def flaggedExtension (Φ : CPTPMap n d) (U : ι → Matrix.unitaryGroup d ℂ) :
    CPTPMap (n × ι) d :=
  CPTPMap.traceRight ∘ₘ CPTPMap.ofUnitary (controlledUnitary U) ∘ₘ
    (Φ ⊗ᶜᵖ CPTPMap.id)

/-- The controlled unitary has the expected action on matrix entries. -/
theorem controlled_conj_entry (U : ι → Matrix.unitaryGroup d ℂ)
    (X : HermitianMat (d × ι) ℂ) (a b : d) (i j : ι) :
    (X.conj (controlledUnitary U).val).mat (a,i) (b,j) =
      ∑ x, ∑ y, (U i).val a x * X.mat (x,i) (y,j) * star ((U j).val b y) := by
  rw [HermitianMat.conj_apply_mat]
  simp [controlledUnitary, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  exact Finset.sum_comm

/-- Basis flags select the corresponding conjugation. -/
theorem flaggedExtension_basis (Φ : CPTPMap n d)
    (U : ι → Matrix.unitaryGroup d ℂ) (ρ : MState n) (i : ι) :
    flaggedExtension Φ U (ρ ⊗ᴹ MState.pure (Ket.basis i)) = (Φ ρ).uConj (U i) := by
  simp only [flaggedExtension, CPTPMap.compose_eq, CPTPMap.prod_apply_prod,
    CPTPMap.id_MState, CPTPMap.ofUnitary_eq_conj, CPTPMap.traceRight_eq_MState_traceRight]
  apply MState.ext_m
  ext a b
  change (∑ j, (((Φ ρ ⊗ᴹ MState.pure (Ket.basis i)).M).conj
    (controlledUnitary U).val).mat (a,j) (b,j)) =
      ((Φ ρ).M.conj (U i).val).mat a b
  simp_rw [controlled_conj_entry]
  rw [HermitianMat.conj_apply_mat]
  change (∑ j, ∑ x, ∑ y, (U j).val a x *
      ((Φ ρ).m x y * (MState.pure (Ket.basis i)).m j j) *
      star ((U j).val b y)) = _
  simp [MState.pure_apply, Ket.basis, Ket.apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul]
  exact Finset.sum_comm


/-- A uniformly mixed-unitary map, represented by its pure-ancilla dilation. -/
def mixedUnitary [Nonempty ι] (U : ι → Matrix.unitaryGroup d ℂ)
    (ρ : MState d) : MState d :=
  ((ρ ⊗ᴹ MState.pure (uniform_superposition : Ket ι)).uConj
    (controlledUnitary U)).traceRight

/-- The entropy cost of this actual mixed-unitary map is at most log of the
number of its uniformly weighted unitaries. -/
theorem entropy_mixedUnitary [Nonempty ι]
    (U : ι → Matrix.unitaryGroup d ℂ) (ρ : MState d) :
    Sᵥₙ (mixedUnitary U ρ) ≤ Sᵥₙ ρ + Real.log (Fintype.card ι) := by
  let σ := (ρ ⊗ᴹ MState.pure (uniform_superposition : Ket ι)).uConj
    (controlledUnitary U)
  have h := Sᵥₙ_triangle_ineq_one_way σ
  have hb := Sᵥₙ_le_log_d σ.traceLeft
  have he : Sᵥₙ σ = Sᵥₙ ρ := by
    rw [entropy_uConj]
    have hup := Sᵥₙ_subadditivity (ρ ⊗ᴹ MState.pure (uniform_superposition : Ket ι))
    have hlo := Sᵥₙ_triangle_ineq_one_way (ρ ⊗ᴹ MState.pure (uniform_superposition : Ket ι))
    simp at hup hlo
    exact le_antisymm hup hlo
  simp only [Finset.card_univ] at hb
  change Sᵥₙ σ.traceRight ≤ _
  linarith

/-- Every entry of the pure uniform-superposition state is the reciprocal
of the dimension. -/
theorem pure_uniform_entry [Nonempty ι] (i j : ι) :
    (MState.pure (uniform_superposition : Ket ι)).m i j =
      ((Fintype.card ι : ℝ)⁻¹ : ℂ) := by
  simp [MState.pure_apply, uniform_superposition, Ket.normalize, Ket.apply,
    ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt]

/-- The dilation is exactly the uniform average of the advertised conjugations. -/
theorem mixedUnitary_eq_average [Nonempty ι]
    (U : ι → Matrix.unitaryGroup d ℂ) (ρ : MState d) :
    mixedUnitary U ρ = average ProbDistribution.uniform (fun i ↦ ρ.uConj (U i)) := by
  apply MState.ext_m
  ext a b
  change (∑ j, (((ρ ⊗ᴹ MState.pure (uniform_superposition : Ket ι)).M).conj
    (controlledUnitary U).val).mat (a,j) (b,j)) = _
  simp_rw [controlled_conj_entry]
  change (∑ j, ∑ x, ∑ y, (U j).val a x *
      (ρ.m x y * (MState.pure (uniform_superposition : Ket ι)).m j j) *
      star ((U j).val b y)) = _
  simp_rw [pure_uniform_entry]
  change _ = (average ProbDistribution.uniform (fun i ↦ ρ.uConj (U i))).M.mat a b
  rw [average_M]
  simp only [HermitianMat.mat_finset_sum, Matrix.sum_apply,
    HermitianMat.mat_smul, Matrix.smul_apply, ProbDistribution.uniform_def,
    Finset.card_univ, one_div, MState.uConj, HermitianMat.conj_apply_mat,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  simp only [Complex.real_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [MState.m, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

/-- Entropy of a uniform mixture of unitary conjugates. -/
theorem entropy_uniform_mixture [Nonempty ι]
    (U : ι → Matrix.unitaryGroup d ℂ) (ρ : MState d) :
    Sᵥₙ (average ProbDistribution.uniform (fun i ↦ ρ.uConj (U i))) ≤
      Sᵥₙ ρ + Real.log (Fintype.card ι) := by
  rw [← mixedUnitary_eq_average]
  exact entropy_mixedUnitary U ρ

end MainHolevo
