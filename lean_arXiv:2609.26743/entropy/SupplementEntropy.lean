import ActualCoordinateMarginal
import ActualTensorBasis
import SingleChannel
import SymbolicAmplification
import TensorCalibration

/-!
# Entropy statements of the supplement

The channels below are actual CPTP maps. Their entry and conjugation equalities
are their defining formulas, not entropy or marginal assumptions. Tensor tuples
are the actual finite tensor products, expressed in an arbitrary finite input
basis. The tensor result allows arbitrary complex unitary factors and filters.
-/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open SuppressorEntropy SuppressorEntropy.TensorMarginal
open EntropyLemmas.BellAlgebra ActualCoordinateMarginal ActualTensorBasis

namespace SupplementEntropy

/-- Lemma 4, including its Bell-input sandwich. -/
theorem lemma4 {n k : ℕ} [Nonempty (Fin n)]
    (hn : 0 < n) (hk : 2 ≤ k)
    (F H : Matrix (Fin n) (Fin n) ℂ) (hF : F.PosSemidef) (hHerm : H.IsHermitian)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hfilter : H * H = (γ : ℂ) • (1 + F)⁻¹)
    (htrace : F.trace.re ≤ n * ε)
    (Φ Φbar : CPTPMap (Fin n) (Fin k))
    (hΦ : ∀ X i j, Φ.map X i j = channelEntry (suppressorK H U) X i j)
    (hconj : ∀ X, Φbar.map X =
      (Φ.map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ)) :
    minimumOutputEntropy (Φ.prod Φbar) ≤
        Sᵥₙ ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))) ∧
      Sᵥₙ ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))) ≤
        referenceEntropy k γ ε := by
  exact ⟨minimumOutputEntropy_le _ _,
    joint_copy_bell_entropy hn hk F H hF hHerm U hU γ ε hγ0 hγ1 hε
      hfilter htrace Φ Φbar hΦ hconj⟩

/-- The actual output-coordinate partial trace commutes with conjugation. -/
lemma coordinateTrace_conjugate {n m r : ℕ}
    (Φ Φbar : CPTPMap (Fin n) (Fin r → Fin m))
    (hconj : ∀ X, Φbar.map X =
      (Φ.map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ))
    (a : Fin r) (X : Matrix (Fin n) (Fin n) ℂ) :
    ((coordinateTraceChannel (α := Fin m) a).compose Φbar).map X =
      (((coordinateTraceChannel (α := Fin m) a).compose Φ).map
        (X.map (starRingEnd ℂ))).map (starRingEnd ℂ) := by
  ext i j
  change (coordinateTraceChannel (α := Fin m) a).map (Φbar.map X) i j = _
  rw [hconj, coordinateTraceChannel_map]
  change (∑ f, star ((Φ.map (X.map (starRingEnd ℂ)))
      ((Equiv.funSplitAt a (Fin m)).symm (i, f))
      ((Equiv.funSplitAt a (Fin m)).symm (j, f)))) =
    star ((coordinateTraceChannel (α := Fin m) a).map
      (Φ.map (X.map (starRingEnd ℂ))) i j)
  rw [coordinateTraceChannel_map, star_sum]

/-- General tensor-coordinate estimate; locality here is the exact tensor
coefficient identity, discharged below for the actual tensor tuple. -/
lemma tensor_bell_entropy_of_cancellation {n m r : ℕ} [Nonempty (Fin n)]
    (hn : 0 < n) (hm : 2 ≤ m)
    (U : (Fin r → Fin m) → Matrix (Fin n) (Fin n) ℂ)
    (V : Fin r → Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hV : ∀ a i, (V a i).conjTranspose * V a i = 1)
    (hlocal : ∀ a I J, (∀ b, b ≠ a → I b = J b) →
      (U J).conjTranspose * U I = (V a (J a)).conjTranspose * V a (I a))
    (F H : Matrix (Fin n) (Fin n) ℂ) (hF : F.PosSemidef) (hHerm : H.IsHermitian)
    (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hfilter : H * H = (γ : ℂ) • (1 + F)⁻¹)
    (htrace : F.trace.re ≤ n * ε)
    (Φ Φbar : CPTPMap (Fin n) (Fin r → Fin m))
    (hΦ : ∀ X I J, Φ.map X I J =
      Matrix.trace ((H * (U J).conjTranspose * U I * H +
        if J = I then 1 - H * H else 0) * X) /
        (Fintype.card (Fin r → Fin m) : ℂ))
    (hconj : ∀ X, Φbar.map X =
      (Φ.map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ)) :
    Sᵥₙ ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))) ≤
      (r : ℝ) * referenceEntropy m γ ε := by
  apply tensor_pair_entropy_from_exact_marginals hn hm F H hF hHerm V hV
    γ ε hγ0 hγ1 hε hfilter htrace Φ Φbar
    (fun a => (coordinateTraceChannel (α := Fin m) a).compose Φ)
    (fun a => (coordinateTraceChannel (α := Fin m) a).compose Φbar)
  · intro a X i j
    change ActualTensorTuple.coordinatePartialTrace a (Φ.map X) i j = _
    simpa only [channelEntry, suppressorK] using
      ActualTensorTuple.coordinate_partial_trace_of_cancellation (by omega : 0 < m)
        U V hlocal H X (Φ.map X) (hΦ X) a i j
  · exact coordinateTrace_conjugate Φ Φbar hconj
  · intro a
    exact paired_channel_coordinate_marginal Φ Φbar _ a

/-- Relabeling each output factor relabels the product output. -/
lemma output_relabel_prod {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq n] [DecidableEq k] (e : k ≃ l) (Φ Ψ : CPTPMap n k) :
    ((CPTPMap.ofEquiv e).compose Φ).prod ((CPTPMap.ofEquiv e).compose Ψ) =
      (CPTPMap.ofEquiv (e.prodCongr e)).compose (Φ.prod Ψ) := by
  apply CPTPMap.ext
  change MatrixMap.kron ((MatrixMap.submatrix ℂ e.symm).comp Φ.map)
    ((MatrixMap.submatrix ℂ e.symm).comp Ψ.map) =
    (MatrixMap.submatrix ℂ (e.prodCongr e).symm).comp (MatrixMap.kron Φ.map Ψ.map)
  rw [MatrixMap.kron_comp_distrib, MatrixMap.submatrix_kron_submatrix]
  rfl

/-- Corollary 1 for the actual tensor tuple, allowing arbitrary complex entries.
The equivalence `e` merely chooses the computational input basis of size `n`.
Taking `e := eInput (Fin d) r` gives exactly `n = d^r`. -/
theorem corollary1 {n M r : ℕ} [Nonempty (Fin n)]
    {d : Type*} [Fintype d] [DecidableEq d]
    (hn : 0 < n) (hM : 2 ≤ M) (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).conjTranspose * T i = 1)
    (F H : Matrix (Fin n) (Fin n) ℂ) (hF : F.PosSemidef) (hHerm : H.IsHermitian)
    (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hfilter : H * H = (γ : ℂ) • (1 + F)⁻¹)
    (htrace : F.trace.re ≤ n * ε)
    (Φ Φbar : CPTPMap (Fin n) (Fin (M ^ r)))
    (hΦ : ∀ X i j, Φ.map X i j =
      channelEntry (suppressorK H (enumeratedTuple e T)) X i j)
    (hconj : ∀ X, Φbar.map X =
      (Φ.map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ)) :
    minimumOutputEntropy (Φ.prod Φbar) ≤
        Sᵥₙ ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))) ∧
      Sᵥₙ ((Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))) ≤
        (r : ℝ) * referenceEntropy M γ ε := by
  refine ⟨minimumOutputEntropy_le _ _, ?_⟩
  let Φt := (CPTPMap.ofEquiv (eOut M r)).compose Φ
  let Φbart := (CPTPMap.ofEquiv (eOut M r)).compose Φbar
  have ht : ∀ X I J, Φt.map X I J =
      Matrix.trace ((H * (reindexedTuple e T J).conjTranspose * reindexedTuple e T I * H +
        if J = I then 1 - H * H else 0) * X) /
        (Fintype.card (Fin r → Fin M) : ℂ) := by
    intro X I J
    change Φ.map X ((eOut M r).symm I) ((eOut M r).symm J) = _
    rw [hΦ]
    simp only [channelEntry, suppressorK, enumeratedTuple_output_inverse,
      Equiv.symm_apply_eq, Equiv.apply_symm_apply,
      Fintype.card_fun, Fintype.card_fin]
  have htconj : ∀ X, Φbart.map X =
      (Φt.map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ) := by
    intro X
    ext I J
    change Φbar.map X ((eOut M r).symm I) ((eOut M r).symm J) = _
    rw [hconj]
    rfl
  have h := tensor_bell_entropy_of_cancellation hn hM
    (reindexedTuple e T) (reindexedCoordinate e T)
    (reindexedCoordinate_unitary e T hT) (reindexed_coordinate_cancellation e T hT)
    F H hF hHerm γ ε hγ0 hγ1 hε hfilter htrace Φt Φbart ht htconj
  simpa only [Φt, Φbart, output_relabel_prod, CPTPMap.compose_eq,
    CPTPMap.ofEquiv_apply, Sᵥₙ_relabel] using h

/-- Corollary 2's exact gap estimate, including the endpoint `c = 1`.
The only norm hypothesis is the stated single-copy suppressor estimate. -/
theorem corollary2 {n M r : ℕ} [Nonempty (Fin n)]
    {d : Type*} [Fintype d] [DecidableEq d]
    (hn : 0 < n) (hM : 2 ≤ M) (hr : 1 ≤ r) (e : Fin n ≃ (Fin r → d))
    (T : Fin M → Matrix d d ℂ) (hT : ∀ i, (T i).conjTranspose * T i = 1)
    (F H : Matrix (Fin n) (Fin n) ℂ) (hF : F.PosSemidef) (hHerm : H.IsHermitian)
    (γ ε c : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) (hc : 1 ≤ c)
    (hfilter : H * H = (γ : ℂ) • (1 + F)⁻¹)
    (htrace : F.trace.re ≤ n * ε)
    (Φ Φbar : CPTPMap (Fin n) (Fin (M ^ r)))
    (hΦ : ∀ X i j, Φ.map X i j =
      channelEntry (suppressorK H (enumeratedTuple e T)) X i j)
    (hconj : ∀ X, Φbar.map X =
      (Φ.map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ))
    (hbound : ∀ W : HermitianMat (Fin (M ^ r)) ℂ, (∀ i, W i i = 0) →
      ‖testObservable H (enumeratedTuple e T) W‖ ≤
        (c * TensorCalibration.tensorScale M r) * γ * ‖W‖) :
    (r : ℝ) * amplificationSlope M (γ ^ 2 / (1 + ε) ^ 2) 9 - 4 * Real.log c ≤
      2 * minimumOutputEntropy Φ - minimumOutputEntropy (Φ.prod Φbar) := by
  have hs := single_copy_lemma H hHerm (enumeratedTuple e T)
    (enumeratedTuple_unitary e T hT) Φ (fun ρ => hΦ ρ.m)
    (c * TensorCalibration.tensorScale M r) γ
    (mul_nonneg (by linarith) (TensorCalibration.scale_pos M r hM hr).le)
    hγ0.le (by positivity : 0 < M ^ r) hbound
  have hnorm : (c * TensorCalibration.tensorScale M r) ^ 2 * γ ^ 2 / (M ^ r : ℕ) =
      γ ^ 2 * c ^ 2 * ((1 + 9 / (M : ℝ)) ^ r - 1) := by
    rw [mul_pow, Nat.cast_pow]
    calc
      c ^ 2 * TensorCalibration.tensorScale M r ^ 2 * γ ^ 2 / (M : ℝ) ^ r =
          γ ^ 2 * c ^ 2 * (TensorCalibration.tensorScale M r ^ 2 / (M : ℝ) ^ r) := by ring
      _ = _ := by rw [TensorCalibration.normalized_scale_sq M r hM hr]
  rw [hnorm, Nat.cast_pow, Real.log_pow] at hs
  have hj := corollary1 hn hM e T hT F H hF hHerm γ ε hγ0 hγ1 hε
    hfilter htrace Φ Φbar hΦ hconj
  exact symbolic_tensor_gap M r (by omega) γ c (γ ^ 2 / (1 + ε) ^ 2)
    (minimumOutputEntropy Φ) (minimumOutputEntropy (Φ.prod Φbar))
    hγ0.le hγ1.le hc hs (by
      simpa only [referenceEntropy_eq_comparisonEntropy] using hj.1.trans hj.2)

/-- The data in Corollary 2 at one tensor exponent, packaged for a family.
Every field is a construction datum or one of the stated hypotheses. -/
structure TensorData (M r : ℕ) (γ ε c : ℝ) where
  n : ℕ
  d : ℕ
  hn : 0 < n
  basis : Fin n ≃ (Fin r → Fin d)
  T : Fin M → Matrix (Fin d) (Fin d) ℂ
  unitary : ∀ i, (T i).conjTranspose * T i = 1
  F : Matrix (Fin n) (Fin n) ℂ
  H : Matrix (Fin n) (Fin n) ℂ
  positive : F.PosSemidef
  hermitian : H.IsHermitian
  filter : H * H = (γ : ℂ) • (1 + F)⁻¹
  trace_bound : F.trace.re ≤ n * ε
  Φ : CPTPMap (Fin n) (Fin (M ^ r))
  Φbar : CPTPMap (Fin n) (Fin (M ^ r))
  entries : ∀ X i j, Φ.map X i j =
    channelEntry (suppressorK H (enumeratedTuple basis T)) X i j
  conjugate : ∀ X, Φbar.map X =
    (Φ.map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ)
  suppressor_bound : ∀ W : HermitianMat (Fin (M ^ r)) ℂ, (∀ i, W i i = 0) →
    ‖testObservable H (enumeratedTuple basis T) W‖ ≤
      (c * TensorCalibration.tensorScale M r) * γ * ‖W‖

/-- The computational input basis has exactly the prescribed tensor size. -/
theorem TensorData.dimension {M r : ℕ} {γ ε c : ℝ}
    (data : TensorData M r γ ε c) : data.n = data.d ^ r := by
  simpa using Fintype.card_congr data.basis

/-- Corollary 2 for a packaged instance; no entropy estimate is a premise. -/
theorem TensorData.gap_bound {M r : ℕ} {γ ε c : ℝ}
    (data : TensorData M r γ ε c)
    (hM : 2 ≤ M) (hr : 1 ≤ r)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) (hc : 1 ≤ c) :
    (r : ℝ) * amplificationSlope M (γ ^ 2 / (1 + ε) ^ 2) 9 - 4 * Real.log c ≤
      2 * minimumOutputEntropy data.Φ - minimumOutputEntropy (data.Φ.prod data.Φbar) := by
  let : Nonempty (Fin data.n) := ⟨⟨0, data.hn⟩⟩
  exact corollary2 data.hn hM hr data.basis data.T data.unitary
    data.F data.H data.positive data.hermitian γ ε c hγ0 hγ1 hε hc
    data.filter data.trace_bound data.Φ data.Φbar data.entries data.conjugate
    data.suppressor_bound

/-- The exact positive-deficit criterion in Corollary 2 makes the actual
minimum-output entropy gaps of any such family unbounded. -/
theorem corollary2_unbounded (M : ℕ) (hM : 2 ≤ M) (γ ε c : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) (hc : 1 ≤ c)
    (hcriterion : 2 * Real.log M - referenceEntropy M γ ε >
      2 * Real.log (1 + 9 / (M : ℝ)))
    (family : ∀ r : ℕ, 1 ≤ r → TensorData M r γ ε c) (target : ℝ) :
    ∃ (r : ℕ) (hr : 1 ≤ r),
      target < 2 * minimumOutputEntropy (family r hr).Φ -
        minimumOutputEntropy ((family r hr).Φ.prod (family r hr).Φbar) := by
  let α := amplificationSlope M (γ ^ 2 / (1 + ε) ^ 2) 9
  have hα : 0 < α := by
    dsimp [α, amplificationSlope]
    rw [referenceEntropy_eq_comparisonEntropy] at hcriterion
    linarith
  obtain ⟨r, hr⟩ := exists_nat_gt (max 0 ((target + 4 * Real.log c) / α))
  have hr0 : (0 : ℝ) < r := (le_max_left _ _).trans_lt hr
  have hrNat : 1 ≤ r := by
    have : 0 < r := by exact_mod_cast hr0
    omega
  have hrt : (target + 4 * Real.log c) / α < (r : ℝ) :=
    (le_max_right _ _).trans_lt hr
  have htarget := (div_lt_iff₀ hα).mp hrt
  have hg := (family r hrNat).gap_bound hM hrNat hγ0 hγ1 hε hc
  refine ⟨r, hrNat, ?_⟩
  change (r : ℝ) * α - 4 * Real.log c ≤ _ at hg
  nlinarith

end SupplementEntropy
