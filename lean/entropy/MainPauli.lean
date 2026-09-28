import MainRandomizer
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Concrete binary Pauli matrices as signed permutation matrices. -/
noncomputable section
open scoped BigOperators ComplexConjugate

namespace MainPauli

abbrev Bits (m : ℕ) := Fin m → ZMod 2

def dotChar {m : ℕ} (b : Bits m) : AddChar (Bits m) ℝ where
  toFun x := MainRandomizer.binarySign (∑ j, b j * x j)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
      AddChar.map_add_eq_mul]

lemma dotChar_apply {m : ℕ} (b x : Bits m) :
    dotChar b x = MainRandomizer.binarySign (∑ j, b j * x j) := rfl

lemma dotChar_comm {m : ℕ} (b x : Bits m) : dotChar b x = dotChar x b := by
  simp only [dotChar_apply, mul_comm]

@[simp] lemma dotChar_zero {m : ℕ} (x : Bits m) : dotChar (0 : Bits m) x = 1 := by
  simp [dotChar_apply]

lemma dotChar_add {m : ℕ} (b c x : Bits m) :
    dotChar (b + c) x = dotChar b x * dotChar c x := by
  simp only [dotChar_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    AddChar.map_add_eq_mul]

@[simp] lemma bits_add_self {m : ℕ} (x : Bits m) : x + x = 0 := by
  ext i
  change x i + x i = 0
  rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

@[simp] lemma dotChar_sq {m : ℕ} (b x : Bits m) : dotChar b x ^ 2 = 1 := by
  rw [pow_two, ← AddChar.map_add_eq_mul, bits_add_self, AddChar.map_zero_eq_one]

lemma dotChar_ne_one {m : ℕ} (b : Bits m) (hb : b ≠ 0) : dotChar b ≠ 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hb
  apply AddChar.ne_one_iff.mpr
  refine ⟨Pi.single j 1, ?_⟩
  simpa [dotChar_apply, Pi.single_apply] using hj

lemma sum_dotChar {m : ℕ} (b : Bits m) :
    ∑ x : Bits m, dotChar b x =
      if b = 0 then (Fintype.card (Bits m) : ℝ) else 0 := by
  classical
  split_ifs with hb
  · simp [hb]
  · exact AddChar.sum_eq_zero_of_ne_one (dotChar_ne_one b hb)

def pauli {m : ℕ} (a b : Bits m) : Matrix (Bits m) (Bits m) ℂ :=
  fun i j => if i = a + j then (dotChar b j : ℂ) else 0

lemma mul_pauli_apply {m : ℕ} (A : Matrix (Bits m) (Bits m) ℂ)
    (a b i j : Bits m) :
    (A * pauli a b) i j = A i (a + j) * (dotChar b j : ℂ) := by
  classical
  simp [Matrix.mul_apply, pauli, mul_ite]

lemma pauli_mul {m : ℕ} (a b c d : Bits m) :
    pauli a b * pauli c d =
      (dotChar b c : ℂ) • pauli (a + c) (b + d) := by
  classical
  ext i j
  rw [mul_pauli_apply]
  simp only [pauli, Matrix.smul_apply, smul_eq_mul, add_assoc,
    AddChar.map_add_eq_mul, dotChar_add, Complex.ofReal_mul]
  split_ifs <;> ring

@[simp] lemma pauli_zero {m : ℕ} : pauli (0 : Bits m) 0 = 1 := by
  classical
  ext i j
  simp [pauli, Matrix.one_apply]

lemma pauli_conjTranspose {m : ℕ} (a b : Bits m) :
    (pauli a b).conjTranspose = (dotChar b a : ℂ) • pauli a b := by
  classical
  ext i j
  simp only [Matrix.conjTranspose_apply, pauli, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = a + j
  · subst i
    have haa : a + (a + j) = j := by rw [← add_assoc, bits_add_self, zero_add]
    simp [haa, AddChar.map_add_eq_mul, Complex.ofReal_mul, pow_two]
  · have hji : j ≠ a + i := by
      intro h
      apply hij
      rw [h, ← add_assoc, bits_add_self, zero_add]
    simp [hij, hji]

theorem pauli_unitary {m : ℕ} (a b : Bits m) :
    (pauli a b).conjTranspose * pauli a b = 1 := by
  rw [pauli_conjTranspose, Matrix.smul_mul, pauli_mul, smul_smul,
    ← Complex.ofReal_mul, ← pow_two, dotChar_sq]
  simp

lemma bits_add_eq_zero_iff {m : ℕ} (a b : Bits m) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun x => x + b) h
    simpa only [add_assoc, bits_add_self, add_zero, zero_add] using this
  · rintro rfl
    exact bits_add_self _

lemma trace_pauli {m : ℕ} (a b : Bits m) :
    Matrix.trace (pauli a b) =
      if a = 0 ∧ b = 0 then (Fintype.card (Bits m) : ℂ) else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    simp only [Matrix.trace, Matrix.diag, pauli, zero_add, ite_true,
      true_and]
    rw [← Complex.ofReal_sum, sum_dotChar]
    split_ifs <;> simp
  · have h (i : Bits m) : i ≠ a + i := by
      intro he
      exact ha (add_right_cancel (he.symm.trans (zero_add i).symm))
    simp [Matrix.trace, Matrix.diag, pauli, h, ha]

def vectorize {m : ℕ} (A : Matrix (Bits m) (Bits m) ℂ) :
    EuclideanSpace ℂ (Bits m × Bits m) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

lemma vectorize_inner {m : ℕ} (A B : Matrix (Bits m) (Bits m) ℂ) :
    inner ℂ (vectorize A) (vectorize B) = Matrix.trace (A.conjTranspose * B) := by
  simp only [PiLp.inner_apply, vectorize, RCLike.inner_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [starRingEnd_apply]
  ring

lemma pauli_inner {m : ℕ} (a b c d : Bits m) :
    inner ℂ (vectorize (pauli a b)) (vectorize (pauli c d)) =
      if (a, b) = (c, d) then (Fintype.card (Bits m) : ℂ) else 0 := by
  classical
  rw [vectorize_inner]
  by_cases he : (a, b) = (c, d)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    simp [pauli_unitary]
  · rw [pauli_conjTranspose, Matrix.smul_mul, pauli_mul, smul_smul,
      Matrix.trace_smul, trace_pauli]
    have h : ¬ (a + c = 0 ∧ b + d = 0) := by
      simpa only [bits_add_eq_zero_iff, Prod.mk.injEq] using he
    simp [he, h]

/-- The normalized Pauli matrices, viewed as a Euclidean matrix basis. -/
def pauliVector {m : ℕ} (v : Bits m × Bits m) : EuclideanSpace ℂ (Bits m × Bits m) :=
  (Real.sqrt (Fintype.card (Bits m)) : ℂ)⁻¹ • vectorize (pauli v.1 v.2)

lemma pauliVector_orthonormal (m : ℕ) :
    Orthonormal ℂ (pauliVector (m := m)) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro v w
  unfold pauliVector
  rw [inner_smul_left, inner_smul_right, pauli_inner]
  have hc : (0 : ℝ) < Fintype.card (Bits m) := by positivity
  have hs : Real.sqrt (Fintype.card (Bits m)) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  simp only [map_inv₀, Complex.conj_ofReal]
  split_ifs with h
  · have hs2 : (Real.sqrt (Fintype.card (Bits m)) : ℂ) ^ 2 =
        (Fintype.card (Bits m) : ℂ) := by
      exact_mod_cast Real.sq_sqrt hc.le
    rw [← hs2]
    field_simp
  · simp

def pauliBasis (m : ℕ) :
    OrthonormalBasis (Bits m × Bits m) ℂ (EuclideanSpace ℂ (Bits m × Bits m)) :=
  (basisOfOrthonormalOfCardEqFinrank (pauliVector_orthonormal m)
    (by simp)).toOrthonormalBasis (by simpa using pauliVector_orthonormal m)

@[simp] lemma pauliBasis_apply (m : ℕ) (v : Bits m × Bits m) :
    pauliBasis m v = pauliVector v := by
  simp [pauliBasis]

lemma conjugate_pauli {m : ℕ} (a b c d : Bits m) :
    pauli c d * pauli a b * (pauli c d).conjTranspose =
      ((dotChar d a * dotChar b c : ℝ) : ℂ) • pauli a b := by
  rw [pauli_conjTranspose, Matrix.mul_smul, pauli_mul, Matrix.smul_mul,
    pauli_mul, smul_smul, smul_smul]
  have hca : c + a + c = a := by
    rw [add_comm c a, add_assoc, bits_add_self, add_zero]
  have hdb : d + b + d = b := by
    rw [add_comm d b, add_assoc, bits_add_self, add_zero]
  rw [hca, hdb, dotChar_add]
  simp only [← Complex.ofReal_mul]
  congr 2
  calc
    _ = dotChar d c ^ 2 * (dotChar d a * dotChar b c) := by ring
    _ = _ := by rw [dotChar_sq, one_mul]

def conjugate {m : ℕ} (v : Bits m × Bits m) :
    Matrix (Bits m) (Bits m) ℂ →ₗ[ℂ] Matrix (Bits m) (Bits m) ℂ where
  toFun A := pauli v.1 v.2 * A * (pauli v.1 v.2).conjTranspose
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' z A := by simp [Matrix.mul_smul, Matrix.smul_mul]

def vectorizeEquiv (m : ℕ) : Matrix (Bits m) (Bits m) ℂ ≃ₗ[ℂ]
    EuclideanSpace ℂ (Bits m × Bits m) where
  toFun := vectorize
  invFun x i j := x (i,j)
  left_inv A := rfl
  right_inv x := rfl
  map_add' A B := rfl
  map_smul' z A := rfl

def average {m : ℕ} {ι : Type*} [Fintype ι] (seed : ι → Bits m × Bits m) :
    Matrix (Bits m) (Bits m) ℂ →ₗ[ℂ] Matrix (Bits m) (Bits m) ℂ :=
  (Fintype.card ι : ℂ)⁻¹ • ∑ t, conjugate (seed t)

def bias {m : ℕ} {ι : Type*} [Fintype ι] (seed : ι → Bits m × Bits m)
    (v : Bits m × Bits m) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ t, dotChar (seed t).2 v.1 * dotChar v.2 (seed t).1

lemma average_pauli {m : ℕ} {ι : Type*} [Fintype ι]
    (seed : ι → Bits m × Bits m) (v : Bits m × Bits m) :
    average seed (pauli v.1 v.2) = (bias seed v : ℂ) • pauli v.1 v.2 := by
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply, conjugate,
    LinearMap.coe_mk, AddHom.coe_mk, conjugate_pauli, ← Finset.sum_smul,
    smul_smul, bias, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_sum]

def averageVector {m : ℕ} {ι : Type*} [Fintype ι] (seed : ι → Bits m × Bits m) :
    EuclideanSpace ℂ (Bits m × Bits m) →ₗ[ℂ] EuclideanSpace ℂ (Bits m × Bits m) :=
  (vectorizeEquiv m).toLinearMap ∘ₗ average seed ∘ₗ (vectorizeEquiv m).symm.toLinearMap

lemma averageVector_pauliBasis {m : ℕ} {ι : Type*} [Fintype ι]
    (seed : ι → Bits m × Bits m) (v : Bits m × Bits m) :
    averageVector seed (pauliBasis m v) =
      (bias seed v : ℂ) • pauliBasis m v := by
  rw [pauliBasis_apply]
  unfold pauliVector
  rw [map_smul]
  change _ • vectorize (average seed (pauli v.1 v.2)) = _
  rw [average_pauli]
  change _ • ((vectorizeEquiv m) (_ • pauli v.1 v.2)) = _
  rw [map_smul, smul_comm]
  rfl

lemma diagonal_repr {κ : Type*} [Fintype κ]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : OrthonormalBasis κ ℂ E) (T : E →ₗ[ℂ] E) (lam : κ → ℂ)
    (he : ∀ j, T (b j) = lam j • b j) (x : E) (i : κ) :
    b.repr (T x) i = lam i * b.repr x i := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, he, smul_smul]
  simp [OrthonormalBasis.repr_self, mul_comm, Pi.single_apply, mul_ite]

/-- Contract the traceless part from the nonidentity Pauli multiplier bound. -/
theorem average_norm_sq_le {m : ℕ} {ι : Type*} [Fintype ι]
    (seed : ι → Bits m × Bits m) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbias : ∀ v : Bits m × Bits m, v ≠ (0,0) → |bias seed v| ≤ δ)
    (A : Matrix (Bits m) (Bits m) ℂ) (hA : Matrix.trace A = 0) :
    ‖vectorize (average seed A)‖ ^ 2 ≤ δ ^ 2 * ‖vectorize A‖ ^ 2 := by
  let b := pauliBasis m
  have hz : b.repr (vectorize A) (0,0) = 0 := by
    rw [OrthonormalBasis.repr_apply_apply]
    simp only [b, pauliBasis_apply, pauliVector, inner_smul_left, pauli_zero,
      vectorize_inner, Matrix.conjTranspose_one, one_mul, hA, mul_zero]
  have hc (v : Bits m × Bits m) :
      ‖b.repr (vectorize (average seed A)) v‖ ^ 2 ≤
        δ ^ 2 * ‖b.repr (vectorize A) v‖ ^ 2 := by
    change ‖b.repr (averageVector seed (vectorize A)) v‖ ^ 2 ≤ _
    rw [diagonal_repr b (averageVector seed) (fun v => (bias seed v : ℂ))
      (averageVector_pauliBasis seed)]
    by_cases hv : v = (0,0)
    · subst v
      simp [hz]
    · rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (hbias v hv) 2) (sq_nonneg _)
  rw [← b.repr.norm_map (vectorize (average seed A)),
    ← b.repr.norm_map (vectorize A), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ => hc v

theorem pauli_unitary_right {m : ℕ} (a b : Bits m) :
    pauli a b * (pauli a b).conjTranspose = 1 := by
  rw [pauli_conjTranspose, Matrix.mul_smul, pauli_mul, smul_smul,
    ← Complex.ofReal_mul, ← pow_two, dotChar_sq]
  simp

@[simp] theorem average_one {m : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (seed : ι → Bits m × Bits m) : average seed 1 = 1 := by
  have hc : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, conjugate, pauli_unitary_right, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, hc]

lemma uniform_bias {m : ℕ} (v : Bits m × Bits m) :
    bias (fun w : Bits m × Bits m => w) v = if v = (0,0) then 1 else 0 := by
  classical
  have hc : (Fintype.card (Bits m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold bias
  simp only [Fintype.sum_prod_type]
  conv_lhs => arg 2; arg 2; intro c; arg 2; intro d; rw [dotChar_comm d v.1]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, sum_dotChar,
    Fintype.card_prod, Nat.cast_mul]
  by_cases ha : v.1 = 0 <;> by_cases hb : v.2 = 0 <;>
    simp [ha, hb, Prod.ext_iff, hc]
  field_simp

def depolarize (m : ℕ) : Matrix (Bits m) (Bits m) ℂ →ₗ[ℂ]
    Matrix (Bits m) (Bits m) ℂ where
  toFun A := ((Fintype.card (Bits m) : ℂ)⁻¹ * Matrix.trace A) • 1
  map_add' A B := by simp [Matrix.trace_add, mul_add, add_smul]
  map_smul' z A := by simp [Matrix.trace_smul, smul_smul, mul_left_comm]

def depolarizeVector (m : ℕ) : EuclideanSpace ℂ (Bits m × Bits m) →ₗ[ℂ]
    EuclideanSpace ℂ (Bits m × Bits m) :=
  (vectorizeEquiv m).toLinearMap ∘ₗ depolarize m ∘ₗ (vectorizeEquiv m).symm.toLinearMap

lemma depolarizeVector_pauliBasis (m : ℕ) (v : Bits m × Bits m) :
    depolarizeVector m (pauliBasis m v) =
      if v = (0,0) then pauliBasis m v else 0 := by
  classical
  have hc : (Fintype.card (Bits m) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [pauliBasis_apply]
  unfold pauliVector
  rw [map_smul]
  change _ • vectorize (depolarize m (pauli v.1 v.2)) = _
  change _ • vectorize (((Fintype.card (Bits m) : ℂ)⁻¹ *
    Matrix.trace (pauli v.1 v.2)) • 1) = _
  rw [trace_pauli]
  by_cases hv : v = (0,0)
  · subst v
    simp [hc]
  · have h : ¬ (v.1 = 0 ∧ v.2 = 0) := by simpa [Prod.ext_iff] using hv
    simp [hv, h, vectorize]
    rfl

/-- Averaging all binary Pauli conjugations is the completely depolarizing map. -/
theorem pauli_twirl {m : ℕ} (A : Matrix (Bits m) (Bits m) ℂ) :
    average (fun v : Bits m × Bits m => v) A =
      ((Fintype.card (Bits m) : ℂ)⁻¹ * Matrix.trace A) • 1 := by
  have h : averageVector (fun v : Bits m × Bits m => v) = depolarizeVector m := by
    apply (pauliBasis m).toBasis.ext
    intro v
    change averageVector _ (pauliBasis m v) = depolarizeVector m (pauliBasis m v)
    rw [averageVector_pauliBasis, uniform_bias, depolarizeVector_pauliBasis]
    split_ifs <;> simp
  have hx := congrArg (fun T => T (vectorize A)) h
  exact (vectorizeEquiv m).injective hx

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]

/-- The two halves of the explicit 2m-bit trace word are the X and Z exponents. -/
def fieldSeed (m : ℕ) (xy : F × F) : Bits m × Bits m :=
  ((fun j => MainRandomizer.codeword F xy.1 xy.2 (Fin.castAdd m j)),
   (fun j => MainRandomizer.codeword F xy.1 xy.2 (Fin.natAdd m j)))

lemma fieldSeed_character {m : ℕ} (v : Bits m × Bits m) (xy : F × F) :
    dotChar (fieldSeed F m xy).2 v.1 * dotChar v.2 (fieldSeed F m xy).1 =
      MainRandomizer.binarySign
        (∑ j : Fin (m + m), Fin.append v.2 v.1 j *
          MainRandomizer.codeword F xy.1 xy.2 j) := by
  rw [Fin.sum_univ_add, AddChar.map_add_eq_mul]
  simp only [Fin.append_left, Fin.append_right, fieldSeed, dotChar_apply]
  rw [mul_comm]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

lemma append_ne_zero {m : ℕ} (v : Bits m × Bits m) (hv : v ≠ (0,0)) :
    Fin.append v.2 v.1 ≠ 0 := by
  intro h
  apply hv
  apply Prod.ext
  · funext j
    have hj := congrFun h (Fin.natAdd m j)
    simpa only [Fin.append_right, Pi.zero_apply] using hj
  · funext j
    have hj := congrFun h (Fin.castAdd m j)
    simpa only [Fin.append_left, Pi.zero_apply] using hj

/-- The actual Pauli multipliers obey the polynomial-root bias bound. -/
theorem fieldSeed_bias {m : ℕ} (v : Bits m × Bits m) (hv : v ≠ (0,0)) :
    |bias (fieldSeed F m) v| ≤ ((m + m - 1 : ℕ) : ℝ) / Fintype.card F := by
  have h := MainRandomizer.codeword_bias_bound F
    (Fin.append v.2 v.1) (append_ne_zero v hv)
  have heq : bias (fieldSeed F m) v = (Fintype.card F : ℝ)⁻¹ ^ 2 *
      ∑ x : F, ∑ y : F, MainRandomizer.binarySign
        (∑ j, Fin.append v.2 v.1 j * MainRandomizer.codeword F x y j) := by
    simp only [bias, fieldSeed_character, Fintype.card_prod, Nat.cast_mul,
      mul_inv_rev, pow_two, Fintype.sum_prod_type]
  rw [heq, abs_of_nonneg h.1]
  exact h.2

/-- The finite-field Pauli average contracts every traceless matrix. -/
theorem fieldSeed_contraction {m : ℕ} (A : Matrix (Bits m) (Bits m) ℂ)
    (hA : Matrix.trace A = 0) :
    ‖vectorize (average (fieldSeed F m) A)‖ ^ 2 ≤
      (((m + m - 1 : ℕ) : ℝ) / Fintype.card F) ^ 2 * ‖vectorize A‖ ^ 2 :=
  average_norm_sq_le (fieldSeed F m) _ (by positivity) (fieldSeed_bias F) A hA

end MainPauli
