import QuantumInfo.Channels.CPTP
import BellAlgebra
import ActualGridFilterProperties

/-!
# A. The suppressor formula defines a quantum channel

The Kraus operators below implement the binary measurement and its two
feedforward branches.  The channel is constructed, rather than postulated
to have the required matrix entries.
-/

noncomputable section
open scoped BigOperators ComplexOrder
open EntropyLemmas.BellAlgebra

namespace MainChannel

variable {n k : ℕ}

/-- The successful measurement branch, resolved in the discarded input basis. -/
def successKraus (V : Fin k → Matrix (Fin n) (Fin n) ℂ) (t : Fin n) :
    Matrix (Fin k) (Fin n) ℂ := fun i a => V i t a

/-- The failure branch prepares a computational basis vector. -/
def failureKraus (G : Matrix (Fin n) (Fin n) ℂ) (jt : Fin k × Fin n) :
    Matrix (Fin k) (Fin n) ℂ := fun i a => if i = jt.1 then G jt.2 a else 0

lemma success_entry (V : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) :
    (MatrixMap.of_kraus (successKraus V) (successKraus V) X) i j =
      (V i * X * (V j).conjTranspose).trace := by
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag_apply, successKraus]

lemma failure_entry (G : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) :
    (MatrixMap.of_kraus (failureKraus G) (failureKraus G) X) i j =
      if i = j then (G * X * G.conjTranspose).trace else 0 := by
  classical
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply, Fintype.sum_prod_type,
    Matrix.mul_apply, Matrix.conjTranspose_apply, failureKraus,
    apply_ite]
  by_cases hij : i = j
  · subst j
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · simp [hij]

/-- The two measurement branches before the common normalization. -/
def rawKraus (H G : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    (Fin n ⊕ (Fin k × Fin n)) → Matrix (Fin k) (Fin n) ℂ :=
  Sum.elim (successKraus (fun i => U i * H)) (failureKraus G)

lemma raw_entry (H G : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) :
    (MatrixMap.of_kraus (rawKraus H G U) (rawKraus H G U) X) i j =
      (U i * H * X * (U j * H).conjTranspose).trace +
        if i = j then (G * X * G.conjTranspose).trace else 0 := by
  have hm : MatrixMap.of_kraus (rawKraus H G U) (rawKraus H G U) =
      MatrixMap.of_kraus (successKraus (fun i => U i * H))
        (successKraus (fun i => U i * H)) +
      MatrixMap.of_kraus (failureKraus G) (failureKraus G) := by
    simp [MatrixMap.of_kraus, rawKraus, Fintype.sum_sum_type]
  rw [hm, LinearMap.add_apply, Matrix.add_apply, success_entry, failure_entry]

/-- The normalized Kraus family of the suppressor channel. -/
def kraus (H G : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (s : Fin n ⊕ (Fin k × Fin n)) : Matrix (Fin k) (Fin n) ℂ :=
  ((Real.sqrt k : ℂ)⁻¹) • rawKraus H G U s

lemma kraus_entry (_hk : 0 < k)
    (H G : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hG : G.IsHermitian)
    (hGsq : G * G = 1 - H * H)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) :
    (MatrixMap.of_kraus (kraus H G U) (kraus H G U) X) i j =
      channelEntry (suppressorK H U) X i j := by
  have hscale : MatrixMap.of_kraus (kraus H G U) (kraus H G U) X =
      (k : ℂ)⁻¹ • MatrixMap.of_kraus (rawKraus H G U) (rawKraus H G U) X := by
    have hsq : (Real.sqrt k : ℂ) ^ 2 = (k : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, kraus, Matrix.conjTranspose_smul,
      Complex.star_def, map_inv₀, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [← pow_two, inv_pow, hsq, Finset.smul_sum]
  rw [hscale, Matrix.smul_apply, raw_entry]
  have ht : (U i * H * X * (U j * H).conjTranspose).trace =
      (H * (U j).conjTranspose * U i * H * X).trace := by
    rw [Matrix.conjTranspose_mul, hH.eq]
    rw [Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  have hg : (G * X * G.conjTranspose).trace = ((1 - H * H) * X).trace := by
    rw [hG.eq, Matrix.trace_mul_cycle, hGsq]
  rw [ht, hg]
  simp only [channelEntry, suppressorK, Matrix.add_mul, Matrix.trace_add]
  by_cases hij : i = j <;> simp [hij, eq_comm, div_eq_mul_inv, mul_add, mul_comm]

/-- The formula (3), with its complete positivity and normalization proved. -/
def suppressor (hk : 0 < k)
    (H G : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hG : G.IsHermitian)
    (hGsq : G * G = 1 - H * H)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1) :
    CPTPMap (Fin n) (Fin k) where
  toLinearMap := MatrixMap.of_kraus (kraus H G U) (kraus H G U)
  cp := MatrixMap.of_kraus_isCompletelyPositive _
  TP := by
    intro X
    simp only [Matrix.trace, Matrix.diag_apply,
      kraus_entry hk H G hH hG hGsq U X]
    simp only [channelEntry, suppressorK_diagonal H U hU,
      Matrix.one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [show (k : ℂ) ≠ 0 by exact_mod_cast hk.ne']
    rfl

lemma suppressor_entry (hk : 0 < k)
    (H G : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hG : G.IsHermitian)
    (hGsq : G * G = 1 - H * H)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) :
    (suppressor hk H G hH hG hGsq U hU).map X i j =
      channelEntry (suppressorK H U) X i j :=
  kraus_entry hk H G hH hG hGsq U X i j

/-- The failed-measurement operator for the actual full-grid construction. -/
def fullGridG (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix (Fin n) (Fin n) ℂ) (L : ℕ) (γ : ℝ) :
    HermitianMat (Fin n) ℂ :=
  (1 - ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ ^ 2).sqrt

lemma fullGridG_sq (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix (Fin n) (Fin n) ℂ) (L : ℕ) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (fullGridG C₁ hC₁ hk C₂ U L γ).mat *
        (fullGridG C₁ hC₁ hk C₂ U L γ).mat =
      1 - (ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ).mat *
        (ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ).mat := by
  have hpos := sub_nonneg.mpr
    (ActualGridFilterProperties.fullGridH_sq_le_one C₁ hC₁ hk C₂ U L γ hγ hγ1)
  simpa only [fullGridG, HermitianMat.mat_sub, HermitianMat.mat_one,
    HermitianMat.mat_pow, pow_two] using HermitianMat.sqrt_sq hpos

/-- The actual basic channel: every parameter fixes a CPTP map. -/
def fullGridChannel (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1) (L : ℕ) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) : CPTPMap (Fin n) (Fin k) :=
  suppressor (by omega)
    (ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ).mat
    (fullGridG C₁ hC₁ hk C₂ U L γ).mat
    (ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ).H
    (fullGridG C₁ hC₁ hk C₂ U L γ).H
    (fullGridG_sq C₁ hC₁ hk C₂ U L γ hγ hγ1) U hU

lemma fullGridChannel_entry (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1) (L : ℕ) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin k) :
    (fullGridChannel C₁ hC₁ hk C₂ U hU L γ hγ hγ1).map X i j =
      channelEntry (suppressorK
        (ActualGridSupport.fullGridH C₁ hC₁ hk C₂ U L γ).mat U) X i j :=
  suppressor_entry ..

#print axioms fullGridChannel
#print axioms fullGridChannel_entry

end MainChannel
