import QuantumInfo.Entropy.SSA
import JointChannel
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Actual tensor-state entropy and marginal coefficients

The marginal states below are defined by actual partial traces. No entropy
subadditivity assumption is introduced. The matrix cancellation result leaves
the global suppressor completely arbitrary.
-/

noncomputable section
open scoped BigOperators Kronecker RealInnerProductSpace InnerProductSpace ComplexOrder
open EntropyLemmas.BellAlgebra EntropyLemmas.TensorBridge

namespace SuppressorEntropy.TensorMarginal

variable {α β : Type*} [Fintype α] [DecidableEq α]

/-- Split the first tensor coordinate from the remaining coordinates. -/
def headTailEquiv (α : Type*) (r : ℕ) :
    α × (Fin r → α) ≃ (Fin (r + 1) → α) where
  toFun x := Fin.cons x.1 x.2
  invFun x := (x 0, Fin.tail x)
  left_inv x := by simp
  right_inv x := Fin.cons_self_tail x

/-- Coordinate marginals, obtained recursively by partial trace. -/
def coordinateMarginal : {r : ℕ} →
    MState (Fin r → α) → Fin r → MState α
  | 0, _, i => Fin.elim0 i
  | r + 1, ρ, i =>
    Fin.cases (ρ.relabel (headTailEquiv α r)).traceRight
      (fun j => coordinateMarginal (ρ.relabel (headTailEquiv α r)).traceLeft j) i

/-- Subadditivity over every coordinate of a genuine multipartite state. -/
theorem entropy_le_sum_coordinateMarginals {r : ℕ}
    (ρ : MState (Fin r → α)) :
    Sᵥₙ ρ ≤ ∑ i : Fin r, Sᵥₙ (coordinateMarginal ρ i) := by
  induction r with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact le_of_eq (Sᵥₙ_unit_zero ρ)
  | succ r ih =>
      let σ := ρ.relabel (headTailEquiv α r)
      have hsub := Sᵥₙ_subadditivity σ
      have htail := ih σ.traceLeft
      rw [Sᵥₙ_relabel] at hsub
      rw [Fin.sum_univ_succ]
      change Sᵥₙ ρ ≤ Sᵥₙ σ.traceRight +
        ∑ i : Fin r, Sᵥₙ (coordinateMarginal σ.traceLeft i)
      exact hsub.trans (add_le_add (le_refl _) htail)

/-- A common entropy bound on the actual coordinate marginals gives the
linear joint-output entropy bound. -/
theorem entropy_le_card_mul_of_marginal_bounds {r : ℕ}
    (ρ : MState (Fin r → α)) (h : ℝ)
    (hmarg : ∀ i, Sᵥₙ (coordinateMarginal ρ i) ≤ h) :
    Sᵥₙ ρ ≤ (r : ℝ) * h := by
  apply (entropy_le_sum_coordinateMarginals ρ).trans
  calc
    ∑ i : Fin r, Sᵥₙ (coordinateMarginal ρ i) ≤ ∑ _ : Fin r, h :=
      Finset.sum_le_sum fun i _ => hmarg i
    _ = (r : ℝ) * h := by simp

/-- Regroup the two outputs by tensor-coordinate pairs. -/
def pairCoordinatesEquiv (α : Type*) (r : ℕ) :
    (Fin r → α × α) ≃ ((Fin r → α) × (Fin r → α)) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun f := fun i => (f.1 i, f.2 i)
  left_inv f := by rfl
  right_inv f := by rfl

/-- Entropy bound for an actual two-copy output after regrouping its
coordinates. There is no product-state assumption. -/
theorem pair_output_entropy_le {r : ℕ}
    (Y : MState ((Fin r → α) × (Fin r → α))) (h : ℝ)
    (hmarg : ∀ i,
      Sᵥₙ (coordinateMarginal (Y.relabel (pairCoordinatesEquiv α r)) i) ≤ h) :
    Sᵥₙ Y ≤ (r : ℝ) * h := by
  have hh := entropy_le_card_mul_of_marginal_bounds
    (Y.relabel (pairCoordinatesEquiv α r)) h hmarg
  simpa only [Sᵥₙ_relabel] using hh

variable [Fintype β] [DecidableEq β]

omit [DecidableEq α] in
/-- Matching spectator unitary factors cancel before any interaction with
the global suppressor. -/
theorem kronecker_spectator_cancels
    (Tᵢ Tⱼ : Matrix α α ℂ) (S : Matrix β β ℂ)
    (hS : S.conjTranspose * S = 1) :
    (Tᵢ ⊗ₖ S).conjTranspose * (Tⱼ ⊗ₖ S) =
      (Tᵢ.conjTranspose * Tⱼ) ⊗ₖ (1 : Matrix β β ℂ) := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hS]

omit [DecidableEq α] in
/-- The cancellation is valid with an arbitrary global suppressor H. -/
theorem global_suppressor_spectator_cancels
    (H : Matrix (α × β) (α × β) ℂ)
    (Tᵢ Tⱼ : Matrix α α ℂ) (S : Matrix β β ℂ)
    (hS : S.conjTranspose * S = 1) :
    H * (Tᵢ ⊗ₖ S).conjTranspose * (Tⱼ ⊗ₖ S) * H =
      H * ((Tᵢ.conjTranspose * Tⱼ) ⊗ₖ (1 : Matrix β β ℂ)) * H := by
  rw [Matrix.mul_assoc H, kronecker_spectator_cancels Tᵢ Tⱼ S hS]

/-- Exact partial-trace identity for the globally suppressed tensor tuple.
The entry assumption is the full defining formula for the output matrix;
the conclusion is its actual matrix partial trace. -/
theorem partial_trace_suppressed_tensor_output
    {m q : ℕ} (hm : m ≠ 0) (hq : q ≠ 0)
    (T : Fin m → Matrix α α ℂ) (S : Fin q → Matrix β β ℂ)
    (hS : ∀ a, (S a).conjTranspose * S a = 1)
    (H X : Matrix (α × β) (α × β) ℂ)
    (Y : Matrix (Fin m × Fin q) (Fin m × Fin q) ℂ)
    (hY : ∀ i a j b,
      Y (i, a) (j, b) =
        Matrix.trace ((H * (T j ⊗ₖ S b).conjTranspose * (T i ⊗ₖ S a) * H +
          if (j, b) = (i, a) then 1 - H * H else 0) * X) /
          ((m : ℂ) * (q : ℂ)))
    (i j : Fin m) :
    Y.traceRight i j =
      Matrix.trace ((H * (((T j).conjTranspose * T i) ⊗ₖ (1 : Matrix β β ℂ)) * H +
        if j = i then 1 - H * H else 0) * X) / (m : ℂ) := by
  change (∑ a : Fin q, Y (i, a) (j, a)) = _
  simp_rw [hY, global_suppressor_spectator_cancels H _ _ _ (hS _)]
  simp only [Prod.mk.injEq, and_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  field_simp

/-- The same exact identity for the actual reduced density matrix. -/
theorem state_marginal_suppressed_tensor_output
    {m q : ℕ} (hm : m ≠ 0) (hq : q ≠ 0)
    (T : Fin m → Matrix α α ℂ) (S : Fin q → Matrix β β ℂ)
    (hS : ∀ a, (S a).conjTranspose * S a = 1)
    (H X : Matrix (α × β) (α × β) ℂ)
    (Y : MState (Fin m × Fin q))
    (hY : ∀ i a j b,
      Y.m (i, a) (j, b) =
        Matrix.trace ((H * (T j ⊗ₖ S b).conjTranspose * (T i ⊗ₖ S a) * H +
          if (j, b) = (i, a) then 1 - H * H else 0) * X) /
          ((m : ℂ) * (q : ℂ)))
    (i j : Fin m) :
    Y.traceRight.m i j =
      Matrix.trace ((H * (((T j).conjTranspose * T i) ⊗ₖ (1 : Matrix β β ℂ)) * H +
        if j = i then 1 - H * H else 0) * X) / (m : ℂ) := by
  change Y.m.traceRight i j = _
  exact partial_trace_suppressed_tensor_output hm hq T S hS H X Y.m hY i j

/-- Taking the right partial trace separately on two systems is exactly
the partial trace over the two spectator systems after regrouping. -/
theorem paired_partial_trace
    (Y : MState ((α × β) × (α × β))) :
    ((CPTPMap.traceRight (d₁ := α) (d₂ := β)).prod
      (CPTPMap.traceRight (d₁ := α) (d₂ := β))) Y =
    (Y.relabel (Equiv.prodProdProdComm α α β β)).traceRight := by
  apply MState.ext_m
  ext ⟨i, j⟩ ⟨i', j'⟩
  change ((CPTPMap.traceRight (d₁ := α) (d₂ := β)).map.kron
    (CPTPMap.traceRight (d₁ := α) (d₂ := β)).map) Y.m (i,j) (i',j') =
    ∑ p : β × β, Y.m ((i,p.1),(j,p.2)) ((i',p.1),(j',p.2))
  have htr (X : Matrix (α × β) (α × β) ℂ) (a b : α) :
      (CPTPMap.traceRight (d₁ := α) (d₂ := β)).map X a b =
        ∑ c : β, X (a,c) (b,c) := rfl
  rw [MatrixMap.kron_def]
  simp_rw [htr]
  simp [Fintype.sum_prod_type, Matrix.single, Prod.mk.injEq, ite_and,
    Finset.mul_sum, Finset.sum_mul]

set_option maxRecDepth 2000 in
/-- Exact naturality of the two-copy marginal for arbitrary channels and
arbitrary joint inputs. It applies in particular to the maximally entangled
input and a channel paired with its entrywise conjugate. -/
theorem paired_channel_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Φ Ψ : CPTPMap ι (α × β)) (X : MState (ι × ι)) :
    (((Φ.prod Ψ) X).relabel (Equiv.prodProdProdComm α α β β)).traceRight =
      (((CPTPMap.traceRight (d₁ := α) (d₂ := β)).compose Φ).prod
        ((CPTPMap.traceRight (d₁ := α) (d₂ := β)).compose Ψ)) X := by
  have hcomp :
      ((CPTPMap.traceRight (d₁ := α) (d₂ := β)).compose Φ).prod
        ((CPTPMap.traceRight (d₁ := α) (d₂ := β)).compose Ψ) =
      ((CPTPMap.traceRight (d₁ := α) (d₂ := β)).prod
        (CPTPMap.traceRight (d₁ := α) (d₂ := β))).compose (Φ.prod Ψ) := by
    apply CPTPMap.ext
    exact MatrixMap.kron_comp_distrib Φ.map _ Ψ.map _
  rw [hcomp, CPTPMap.compose_eq, paired_partial_trace]

/-- The Bell input itself satisfies the joint entropy bound. This strengthens
the minimum-output conclusion in `JointChannel` using the same full proof. -/
theorem joint_copy_bell_entropy {n k : ℕ} [Nonempty (Fin n)]
    (hn : 0 < n) (hk : 2 ≤ k)
    (F H : Matrix (Fin n) (Fin n) ℂ) (hF : F.PosSemidef) (hHerm : H.IsHermitian)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hH : H * H = (γ : ℂ) • (1 + F)⁻¹)
    (htrace : F.trace.re ≤ n * ε)
    (Φ Φbar : CPTPMap (Fin n) (Fin k))
    (hΦ : ∀ X i j, Φ.map X i j = channelEntry (suppressorK H U) X i j)
    (hconj : ∀ X, Φbar.map X =
      (Φ.map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ)) :
    Sᵥₙ ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))) ≤
      referenceEntropy k γ ε := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hk0 : 0 < k := by omega
  have : Nonempty (Fin k) := ⟨⟨0, hk0⟩⟩
  let σ := (Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))
  let P := diagonalTensorProjection k
  let E := bellProjection k
  let s := γ^2/(1+ε)^2
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs1 : s < 1 := by
    apply (div_lt_one (by positivity : 0 < (1+ε)^2)).mpr
    nlinarith
  have hbar := conjugate_matrix_unit_entries Φ Φbar (suppressorK H U) hΦ hconj
  have hsym := suppressorK_conjTranspose H U hHerm.eq
  have hdiag := product_bell_diagonal Φ Φbar (suppressorK H U) hΦ hbar hsym
    (suppressorK_diagonal H U hU) hn.ne'
  have hmass : ⟪σ.M,P⟫_ℝ = 1/(k:ℝ) :=
    inner_diagonalTensorProjection_of_uniform σ hk0.ne' hdiag
  have hq : (1+s*((k:ℝ)-1))/(k:ℝ)^2 ≤ ⟪σ.M,E⟫_ℝ := by
    rw [show ⟪σ.M,E⟫_ℝ = (bellOverlap (suppressorK H U)).re from
      product_bell_inner Φ Φbar (suppressorK H U) hΦ hbar hsym]
    exact suppressor_bellOverlap_lower hn hk0 F H hF hHerm U hU γ ε
      hγ0.le hε.le hH htrace
  have hentropy := entropy_le_bell_projections σ P E
    (diagonalTensorProjection_idempotent k) (bellProjection_idempotent k)
    (diagonalTensorProjection_mul_bellProjection k)
    (bellProjection_mul_diagonalTensorProjection k)
    k hk (by simp [pow_two]) (diagonalTensorProjection_trace k)
    (bellProjection_trace k) s hs0 hs1 hmass hq
  exact hentropy


/-- The tensor-coordinate comparison for actual channels, given the exact
coordinate-channel identities. All entropy estimates are derived internally.
The two families of equalities specify the marginal channel entries and the
coordinate-pair marginals of the joint output; they are not entropy hypotheses. -/
theorem tensor_pair_entropy_from_exact_marginals
    {n m r : ℕ} [Nonempty (Fin n)]
    (hn : 0 < n) (hm : 2 ≤ m)
    (F H : Matrix (Fin n) (Fin n) ℂ) (hF : F.PosSemidef) (hHerm : H.IsHermitian)
    (V : Fin r → Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hV : ∀ a i, (V a i).conjTranspose * V a i = 1)
    (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hH : H * H = (γ : ℂ) • (1 + F)⁻¹)
    (htrace : F.trace.re ≤ n * ε)
    (Φ Φbar : CPTPMap (Fin n) (Fin r → Fin m))
    (Φa Φbara : Fin r → CPTPMap (Fin n) (Fin m))
    (hΦa : ∀ a X i j,
      (Φa a).map X i j = channelEntry (suppressorK H (V a)) X i j)
    (hconja : ∀ a X, (Φbara a).map X =
      ((Φa a).map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ))
    (hmarg : ∀ a,
      coordinateMarginal
        (((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))).relabel
          (pairCoordinatesEquiv (Fin m) r)) a =
      ((Φa a).prod (Φbara a)) (MState.pure (Ket.MES (Fin n)))) :
    Sᵥₙ ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))) ≤
      (r : ℝ) * referenceEntropy m γ ε := by
  apply pair_output_entropy_le
  intro a
  rw [hmarg]
  exact joint_copy_bell_entropy hn hm F H hF hHerm (V a) (hV a)
    γ ε hγ0 hγ1 hε hH htrace (Φa a) (Φbara a) (hΦa a) (hconja a)

#print axioms paired_channel_marginal
#print axioms paired_partial_trace
#print axioms tensor_pair_entropy_from_exact_marginals
#print axioms joint_copy_bell_entropy
#print axioms entropy_le_sum_coordinateMarginals
#print axioms pair_output_entropy_le
#print axioms global_suppressor_spectator_cancels
#print axioms partial_trace_suppressed_tensor_output
#print axioms state_marginal_suppressed_tensor_output

end SuppressorEntropy.TensorMarginal
