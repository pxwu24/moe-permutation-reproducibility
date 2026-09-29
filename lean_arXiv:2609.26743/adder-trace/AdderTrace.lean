import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.CoprodI
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Basic

/-!
Complete Lean verification of the explicit-filter trace proposition.

Main theorem: AdderTrace.technical_trace_bound.
Its only assumptions are the numerical hypotheses in the question. It uses
the actual modular adder matrices and the entire Gaussian-integer grid.
AdderTrace.prescribedFilter_trace_real identifies the real part used for the
ordered inequality with the actual complex trace.

Checked with Lean 4.24.0 and mathlib v4.24.0,
commit f897ebcf72cd16f89ab4577d0c826cd14afaafc7.

Run: lake env lean AdderTrace.lean
-/

/-! Source component: FreeBound.lean -/

/-!
# The scalar support-set estimate behind the free tensor bound

This file proves the binomial/Cauchy--Schwarz part of the estimate. The
actual free-group cancellation and tensor convolution estimates are
developed in `PrefixOperators`, `HomogeneousTensor`, and `FullTensorBound`.
-/

open scoped BigOperators

namespace ExplicitFilter

/-- The elementary Frobenius-norm estimate, written without operator-norm
infrastructure. -/
theorem matrix_l2_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → κ → ℂ) (f : κ → ℂ) :
    (∑ i, ‖∑ j, C i j * f j‖ ^ 2) ≤
      (∑ i, ∑ j, ‖C i j‖ ^ 2) * (∑ j, ‖f j‖ ^ 2) := by
  classical
  have hrow (i : ι) : ‖∑ j, C i j * f j‖ ^ 2 ≤
      (∑ j, ‖C i j‖ ^ 2) * (∑ j, ‖f j‖ ^ 2) := by
    have hnorm : ‖∑ j, C i j * f j‖ ≤
        Real.sqrt (∑ j, ‖C i j‖ ^ 2) * Real.sqrt (∑ j, ‖f j‖ ^ 2) := by
      calc
        ‖∑ j, C i j * f j‖ ≤ ∑ j, ‖C i j * f j‖ := norm_sum_le _ _
        _ = ∑ j, ‖C i j‖ * ‖f j‖ := by simp only [norm_mul]
        _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    calc
      ‖∑ j, C i j * f j‖ ^ 2 ≤
          (Real.sqrt (∑ j, ‖C i j‖ ^ 2) * Real.sqrt (∑ j, ‖f j‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm _
      _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  calc
    (∑ i, ‖∑ j, C i j * f j‖ ^ 2) ≤
        ∑ i, (∑ j, ‖C i j‖ ^ 2) * (∑ j, ‖f j‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by rw [Finset.sum_mul]

/-- The same coefficient matrix can act independently on any finite
number of suffix spaces without changing its Frobenius constant. -/
theorem matrix_l2_bound_with_suffix {ι κ ζ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ζ]
    (C : ι → κ → ℂ) (f : ζ → κ → ℂ) :
    (∑ z, ∑ i, ‖∑ j, C i j * f z j‖ ^ 2) ≤
      (∑ i, ∑ j, ‖C i j‖ ^ 2) * (∑ z, ∑ j, ‖f z j‖ ^ 2) := by
  calc
    (∑ z, ∑ i, ‖∑ j, C i j * f z j‖ ^ 2) ≤
        ∑ z, (∑ i, ∑ j, ‖C i j‖ ^ 2) * (∑ j, ‖f z j‖ ^ 2) :=
      Finset.sum_le_sum (fun z _ => matrix_l2_bound C (f z))
    _ = _ := by rw [Finset.mul_sum]

/-- The nonempty subsets of the tensor coordinates. -/
def nonemptySupports (r : ℕ) : Finset (Finset (Fin r)) :=
  (Finset.univ : Finset (Fin r)).powerset.erase ∅

theorem mem_nonemptySupports {r : ℕ} {S : Finset (Fin r)} :
    S ∈ nonemptySupports r ↔ S ≠ ∅ := by
  classical
  simp [nonemptySupports]

/-- The binomial identity which gives the exact constant in the proposition. -/
theorem sum_support_weights (M : ℝ) (r : ℕ) :
    (∑ S ∈ nonemptySupports r, (9 : ℝ) ^ S.card * M ^ (r - S.card)) =
      (M + 9) ^ r - M ^ r := by
  classical
  have hfull :
      (∑ S ∈ (Finset.univ : Finset (Fin r)).powerset,
        (9 : ℝ) ^ S.card * M ^ (r - S.card)) = (M + 9) ^ r := by
    simpa [Finset.prod_const, Finset.card_sdiff, add_comm] using
      (Finset.prod_add (fun _ : Fin r => (9 : ℝ)) (fun _ => M) Finset.univ).symm
  have hzero : (∅ : Finset (Fin r)) ∈ (Finset.univ : Finset (Fin r)).powerset :=
    Finset.mem_powerset.mpr (Finset.empty_subset _)
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (Fin r)).powerset)
    (f := fun S => (9 : ℝ) ^ S.card * M ^ (r - S.card)) hzero
  simp only [Finset.card_empty, pow_zero, Nat.sub_zero, one_mul] at hsplit
  rw [hfull] at hsplit
  dsimp [nonemptySupports]
  linarith

/-- Cauchy--Schwarz combines all nonempty coordinate supports with the
constant `sqrt ((M+9)^r-M^r)`. -/
theorem support_cauchy_schwarz (M : ℝ) (hM : 0 ≤ M) (r : ℕ)
    (a : Finset (Fin r) → ℝ) :
    (∑ S ∈ nonemptySupports r,
      Real.sqrt ((9 : ℝ) ^ S.card * M ^ (r - S.card)) * a S) ≤
      Real.sqrt ((M + 9) ^ r - M ^ r) *
        Real.sqrt (∑ S ∈ nonemptySupports r, (a S) ^ 2) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (nonemptySupports r)
    (fun S => Real.sqrt ((9 : ℝ) ^ S.card * M ^ (r - S.card))) a
  have hsqrt (S : Finset (Fin r)) :
      Real.sqrt ((9 : ℝ) ^ S.card * M ^ (r - S.card)) ^ 2 =
        (9 : ℝ) ^ S.card * M ^ (r - S.card) := Real.sq_sqrt (by positivity)
  simp only [hsqrt] at hcs
  rwa [sum_support_weights] at hcs

/-- Equivalent expression of the individual support weight. -/
theorem sqrt_support_weight (M : ℝ) (hM : 0 ≤ M) (r s : ℕ) :
    Real.sqrt ((9 : ℝ) ^ s * M ^ (r - s)) =
      (3 : ℝ) ^ s * Real.sqrt (M ^ (r - s)) := by
  rw [Real.sqrt_mul (by positivity)]
  have hsq : (9 : ℝ) ^ s = ((3 : ℝ) ^ s) ^ 2 := by
    rw [← pow_mul, mul_comm s 2, pow_mul]
    norm_num
  rw [hsq, Real.sqrt_sq (by positivity)]

/-- A finite sum of normed-space vectors with the stated individual
support bounds satisfies the desired Delta bound. This is a generic
aggregation theorem; its hypotheses are the individual estimates. -/
theorem norm_sum_le_delta {E : Type*} [SeminormedAddCommGroup E]
    (M : ℝ) (hM : 0 ≤ M) (r : ℕ)
    (v : Finset (Fin r) → E) (a : Finset (Fin r) → ℝ)
    (hv : ∀ S ∈ nonemptySupports r,
      ‖v S‖ ≤ (3 : ℝ) ^ S.card * Real.sqrt (M ^ (r - S.card)) * a S) :
    ‖∑ S ∈ nonemptySupports r, v S‖ ≤
      Real.sqrt ((M + 9) ^ r - M ^ r) *
        Real.sqrt (∑ S ∈ nonemptySupports r, (a S) ^ 2) := by
  calc
    ‖∑ S ∈ nonemptySupports r, v S‖ ≤
        ∑ S ∈ nonemptySupports r, ‖v S‖ := norm_sum_le _ _
    _ ≤ ∑ S ∈ nonemptySupports r,
        Real.sqrt ((9 : ℝ) ^ S.card * M ^ (r - S.card)) * a S := by
      apply Finset.sum_le_sum
      intro S hS
      simpa [sqrt_support_weight M hM] using hv S hS
    _ ≤ _ := support_cauchy_schwarz M hM r a

end ExplicitFilter


/-! Source component: FinsuppL2.lean -/

open scoped BigOperators

namespace ExplicitFilter

noncomputable section

/-- Squared Euclidean norm of a finitely supported complex vector. -/
def l2Sq {α : Type*} (f : α →₀ ℂ) : ℝ :=
  ∑ x ∈ f.support, ‖f x‖ ^ 2

theorem l2Sq_nonneg {α : Type*} (f : α →₀ ℂ) : 0 ≤ l2Sq f := by
  unfold l2Sq
  positivity

theorem l2Sq_eq_sum {α : Type*} (f : α →₀ ℂ) (s : Finset α)
    (hs : f.support ⊆ s) : l2Sq f = ∑ x ∈ s, ‖f x‖ ^ 2 := by
  classical
  unfold l2Sq
  apply Finset.sum_subset hs
  intro x hx hnot
  simp [Finsupp.notMem_support_iff.mp hnot]

/-- Relabeling distinct coordinates preserves the squared Euclidean norm. -/
theorem l2Sq_embDomain {α β : Type*} (e : α ↪ β) (f : α →₀ ℂ) :
    l2Sq (Finsupp.embDomain e f) = l2Sq f := by
  classical
  simp only [l2Sq, Finsupp.support_embDomain, Finset.sum_map,
    Finsupp.embDomain_apply]

/-- Pulling coordinates back along an injection is a contraction. -/
theorem l2Sq_comapDomain_le {α β : Type*} (e : α ↪ β) (f : β →₀ ℂ) :
    l2Sq (Finsupp.comapDomain e f e.injective.injOn) ≤ l2Sq f := by
  classical
  let g := Finsupp.comapDomain e f e.injective.injOn
  have hsub : g.support.map e ⊆ f.support := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa [g, Finsupp.mem_support_iff] using hy
  calc
    l2Sq g = ∑ x ∈ g.support.map e, ‖f x‖ ^ 2 := by
      simp [l2Sq, Finset.sum_map, g]
    _ ≤ l2Sq f := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => sq_nonneg _)

/-- A coordinate projection is a contraction. -/
theorem l2Sq_filter_le {α : Type*} (p : α → Prop) [DecidablePred p]
    (f : α →₀ ℂ) : l2Sq (f.filter p) ≤ l2Sq f := by
  classical
  calc
    l2Sq (f.filter p) = ∑ x ∈ f.support.filter p, ‖f x‖ ^ 2 := by
      unfold l2Sq
      rw [Finsupp.support_filter]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hx).2]
    _ ≤ l2Sq f := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => sq_nonneg _)

/-- Elementary finite-vector estimate, used to add cancellation pieces. -/
theorem norm_sum_sq_le_card_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hnorm := norm_sum_le s f
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hcs
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm _
    _ ≤ _ := by simpa [mul_comm] using hcs

/-- A sum of `N` finitely supported vectors has squared norm at most
`N` times the sum of their squared norms. -/
theorem l2Sq_sum_le {α ι : Type*} (s : Finset ι) (f : ι → α →₀ ℂ) :
    l2Sq (∑ i ∈ s, f i) ≤ (s.card : ℝ) * ∑ i ∈ s, l2Sq (f i) := by
  classical
  let S := s.biUnion (fun i => (f i).support)
  have hmem (i : ι) (hi : i ∈ s) : (f i).support ⊆ S := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
  have hsub : (∑ i ∈ s, f i).support ⊆ S := by
    intro x hx
    by_contra hnot
    have hfzero : ∀ i ∈ s, f i x = 0 := by
      intro i hi
      apply Finsupp.notMem_support_iff.mp
      exact fun hx => hnot (hmem i hi hx)
    have hz : (∑ i ∈ s, f i) x = 0 := by
      simpa using Finset.sum_eq_zero hfzero
    exact Finsupp.mem_support_iff.mp hx hz
  rw [l2Sq_eq_sum _ S hsub]
  calc
    (∑ x ∈ S, ‖(∑ i ∈ s, f i) x‖ ^ 2) ≤
        ∑ x ∈ S, (s.card : ℝ) * ∑ i ∈ s, ‖f i x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      simpa using norm_sum_sq_le_card_sum s (fun i => f i x)
    _ = (s.card : ℝ) * ∑ i ∈ s, ∑ x ∈ S, ‖f i x‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (l2Sq_eq_sum (f i) S (hmem i hi)).symm

/-- A matrix acting on a finite family of coordinates, leaving the suffix
coordinate unchanged. -/
def blockMatrix {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → κ → ℂ) (f : (κ × ζ) →₀ ℂ) : (ι × ζ) →₀ ℂ := by
  classical
  refine Finsupp.onFinset (Finset.univ.product (f.support.image Prod.snd))
    (fun iz => ∑ j, C iz.1 j * f (j, iz.2)) ?_
  intro iz hne
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, true_and]
  by_contra hnot
  apply hne
  apply Finset.sum_eq_zero
  intro j hj
  have hf : f (j, iz.2) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hin
    exact hnot (Finset.mem_image.mpr ⟨(j, iz.2), hin, rfl⟩)
  simp [hf]

@[simp] theorem blockMatrix_apply {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → κ → ℂ) (f : (κ × ζ) →₀ ℂ) (i : ι) (z : ζ) :
    blockMatrix C f (i, z) = ∑ j, C i j * f (j, z) := rfl

/-- The Frobenius estimate is unchanged by arbitrarily many suffix
coordinates, including infinitely many possible suffixes. -/
theorem l2Sq_blockMatrix_le {ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → κ → ℂ) (f : (κ × ζ) →₀ ℂ) :
    l2Sq (blockMatrix C f) ≤ (∑ i, ∑ j, ‖C i j‖ ^ 2) * l2Sq f := by
  classical
  let Z := f.support.image Prod.snd
  have hin : f.support ⊆ Finset.univ.product Z := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  have hout : (blockMatrix C f).support ⊆ Finset.univ.product Z := by
    exact Finsupp.support_onFinset_subset
  rw [l2Sq_eq_sum _ _ hout, l2Sq_eq_sum _ _ hin]
  simp only [Finset.product_eq_sprod, Finset.sum_product, blockMatrix_apply]
  rw [Finset.sum_comm (s := Finset.univ) (t := Z)]
  calc
    (∑ z ∈ Z, ∑ i, ‖∑ j, C i j * f (j, z)‖ ^ 2) ≤
        ∑ z ∈ Z, (∑ i, ∑ j, ‖C i j‖ ^ 2) * (∑ j, ‖f (j, z)‖ ^ 2) :=
      Finset.sum_le_sum (fun z hz => matrix_l2_bound C (fun j => f (j, z)))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm

/-- A coefficient matrix placed between two injective prefix maps obeys
the same Frobenius bound. This includes every fixed cancellation pattern. -/
theorem l2Sq_prefix_matrix_le {α ι κ ζ : Type*} [Fintype ι] [Fintype κ]
    (left : (ι × ζ) ↪ α) (right : (κ × ζ) ↪ α)
    (C : ι → κ → ℂ) (f : α →₀ ℂ) :
    l2Sq (Finsupp.embDomain left
      (blockMatrix C (Finsupp.comapDomain right f right.injective.injOn))) ≤
        (∑ i, ∑ j, ‖C i j‖ ^ 2) * l2Sq f := by
  rw [l2Sq_embDomain]
  exact (l2Sq_blockMatrix_le _ _).trans
    (mul_le_mul_of_nonneg_left (l2Sq_comapDomain_le right f) (by positivity))

end
end ExplicitFilter


/-! Source component: PrefixOperators.lean -/

/-!
Elementary reduced-word cancellation identities used in the three-piece estimate.
-/

namespace AdderTrace
namespace PrefixOperators

variable {α : Type*} [DecidableEq α]

abbrev Word (α : Type*) := List (α × Bool)

/-- Prefixing `g_i⁻¹ g_j` has exactly three possibilities: zero, one,
or two cancellations. The Boolean `true` denotes a generator. -/
def pairAction (i j : α) (w : Word α) : Word α :=
  match w with
  | [] => [(i, false), (j, true)]
  | (a, b) :: tail =>
    if j = a ∧ b = false then
      match tail with
      | [] => [(i, false)]
      | (c, d) :: rest =>
        if i = c ∧ d = true then rest else (i, false) :: tail
    else (i, false) :: (j, true) :: w

/-- An exact, entirely combinatorial cancellation formula. -/
theorem reduce_pair (i j : α) (hij : i ≠ j) (w : Word α)
    (hw : FreeGroup.IsReduced w) :
    FreeGroup.reduce ((i, false) :: (j, true) :: w) = pairAction i j w := by
  have hr := hw.reduce_eq
  simp only [FreeGroup.reduce.cons, hr]
  cases w with
  | nil => simp [pairAction, hij]
  | cons x tail =>
    rcases x with ⟨a, b⟩
    cases tail with
    | nil =>
      cases b <;> by_cases haj : j = a <;> simp_all [pairAction]
    | cons y rest =>
      rcases y with ⟨c, d⟩
      cases b <;> cases d <;> by_cases haj : j = a <;> by_cases hci : i = c <;>
        simp_all [pairAction]

/-- The formula applies to the canonical reduced word of every free-group element. -/
theorem toWord_pair_mul (i j : α) (hij : i ≠ j) (g : FreeGroup α) :
    ((FreeGroup.of i)⁻¹ * FreeGroup.of j * g).toWord =
      pairAction i j g.toWord := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mul, FreeGroup.toWord_inv]
  simp only [FreeGroup.toWord_of]
  have hpair : FreeGroup.reduce (FreeGroup.invRev [(i, true)] ++ [(j, true)]) =
      [(i, false), (j, true)] := by
    simp [FreeGroup.invRev, FreeGroup.reduce.cons, hij]
  rw [hpair]
  exact reduce_pair i j hij g.toWord FreeGroup.isReduced_toWord


noncomputable section

/-- Prefix creation on a basis vector, with value zero if it would cancel. -/
def createBasis (v w : Word α) : Word α →₀ ℂ := by
  classical
  exact if FreeGroup.IsReduced (v ++ w) then Finsupp.single (v ++ w) 1 else 0

/-- Prefix removal on a basis vector, with value zero if the prefix is absent. -/
def eraseBasis (v w : Word α) : Word α →₀ ℂ := by
  classical
  exact if v <+: w then Finsupp.single (w.drop v.length) 1 else 0

/-- The one-cancellation piece. -/
def middleBasis (i j : α) (w : Word α) : Word α →₀ ℂ := by
  classical
  exact if [(j, false)] <+: w then createBasis [(i, false)] w.tail else 0

/-- Exact three-piece decomposition on each reduced-word basis vector. -/
theorem three_piece_basis (i j : α) (hij : i ≠ j) (w : Word α)
    (hw : FreeGroup.IsReduced w) :
    Finsupp.single (FreeGroup.reduce ((i, false) :: (j, true) :: w)) (1 : ℂ) =
      createBasis [(i, false), (j, true)] w + middleBasis i j w +
        eraseBasis [(j, false), (i, true)] w := by
  classical
  rw [reduce_pair i j hij w hw]
  cases w with
  | nil =>
    simp [pairAction, createBasis, middleBasis, eraseBasis, FreeGroup.IsReduced,
      List.isChain_cons_cons, hij]
  | cons x tail =>
    rcases x with ⟨a, b⟩
    cases tail with
    | nil =>
      cases b <;>
        simp [pairAction, createBasis, middleBasis, eraseBasis, FreeGroup.IsReduced,
          List.isChain_cons_cons, eq_comm, hij] <;>
        split_ifs <;> simp_all
    | cons y rest =>
      rcases y with ⟨c, d⟩
      cases b <;> cases d <;>
        simp only [FreeGroup.isReduced_cons_cons, Prod.mk.injEq,
          Bool.false_eq_true, Bool.true_eq_false] at hw ⊢ <;>
        simp [pairAction, createBasis, middleBasis, eraseBasis, FreeGroup.IsReduced,
          List.isChain_cons_cons, eq_comm, hij] <;>
        (try split_ifs) <;> simp_all [FreeGroup.IsReduced, List.isChain_cons_cons]


/-- The removal kernel is the transpose of the creation kernel on reduced words.
Since both kernels are real-valued, this is also the adjoint relation. -/
theorem eraseBasis_transpose (v w y : Word α) (hw : FreeGroup.IsReduced w) :
    eraseBasis v w y = createBasis v y w := by
  classical
  by_cases heq : v ++ y = w
  · subst w
    simp [eraseBasis, createBasis, hw]
  · have hsingle : (Finsupp.single (v ++ y) (1 : ℂ)) w = 0 := by
      exact Finsupp.single_eq_of_ne (Ne.symm heq)
    simp only [createBasis]
    split_ifs with hred
    all_goals
      simp only [hsingle, Finsupp.zero_apply]
      simp only [eraseBasis]
      split_ifs with hp
      · have hne : w.drop v.length ≠ y := by
          intro h
          apply heq
          rw [← h]
          exact List.prefix_iff_eq_append.mp hp
        exact Finsupp.single_eq_of_ne hne.symm
      · rfl

/-- Linear extension of prefix creation. -/
def create (v : Word α) : (Word α →₀ ℂ) →ₗ[ℂ] (Word α →₀ ℂ) :=
  Finsupp.linearCombination ℂ (createBasis v)

/-- Linear extension of prefix removal. -/
def erase (v : Word α) : (Word α →₀ ℂ) →ₗ[ℂ] (Word α →₀ ℂ) :=
  Finsupp.linearCombination ℂ (eraseBasis v)

/-- Prefix replacement equals a creation followed by a removal. -/
theorem middleBasis_eq_comp (i j : α) (w : Word α) :
    middleBasis i j w = create [(i, false)] (eraseBasis [(j, false)] w) := by
  classical
  by_cases h : [(j, false)] <+: w
  · simp [middleBasis, eraseBasis, h, create, List.drop_one]
  · simp [middleBasis, eraseBasis, h]

/-- Creation and annihilation decomposition in operator form on a basis vector. -/
theorem three_piece_operators (i j : α) (hij : i ≠ j) (w : Word α)
    (hw : FreeGroup.IsReduced w) :
    Finsupp.single (FreeGroup.reduce ((i, false) :: (j, true) :: w)) (1 : ℂ) =
      create [(i, false), (j, true)] (Finsupp.single w 1) +
      create [(i, false)] (erase [(j, false)] (Finsupp.single w 1)) +
      erase [(j, false), (i, true)] (Finsupp.single w 1) := by
  have h := three_piece_basis i j hij w hw
  rw [middleBasis_eq_comp] at h
  simpa only [create, erase, Finsupp.linearCombination_single, one_smul] using h


/-- Unguarded creation on the full list Fock space. -/
def pureCreate (v : Word α) : (Word α →₀ ℂ) →ₗ[ℂ] (Word α →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun w => Finsupp.single (v ++ w) 1)

/-- Orthogonal coordinate projection onto the reduced words. -/
def reducedProjection : (Word α →₀ ℂ) →ₗ[ℂ] (Word α →₀ ℂ) := by
  classical
  exact Finsupp.linearCombination ℂ (fun w =>
    if FreeGroup.IsReduced w then Finsupp.single w 1 else 0)

/-- Guarded creation is just pure creation followed by the reduced-word projection. -/
theorem createBasis_eq_projection (v w : Word α) :
    createBasis v w = reducedProjection (pureCreate v (Finsupp.single w 1)) := by
  classical
  simp [createBasis, pureCreate, reducedProjection]


/-- Removing a prefix from a reduced word leaves a reduced word. -/
theorem reducedProjection_eraseBasis (v w : Word α) (hw : FreeGroup.IsReduced w) :
    reducedProjection (eraseBasis v w) = eraseBasis v w := by
  classical
  have hd : FreeGroup.IsReduced (w.drop v.length) := hw.drop _
  by_cases h : v <+: w
  · simp [eraseBasis, h, reducedProjection, hd]
  · simp [eraseBasis, h]

/-- A reduced-word basis identity using only unguarded Fock-space creators. -/
theorem three_piece_fock (i j : α) (hij : i ≠ j) (w : Word α)
    (hw : FreeGroup.IsReduced w) :
    Finsupp.single (FreeGroup.reduce ((i, false) :: (j, true) :: w)) (1 : ℂ) =
      reducedProjection (pureCreate [(i, false), (j, true)] (Finsupp.single w 1)) +
      reducedProjection (pureCreate [(i, false)]
        (erase [(j, false)] (Finsupp.single w 1))) +
      erase [(j, false), (i, true)] (Finsupp.single w 1) := by
  classical
  rw [three_piece_basis i j hij w hw, createBasis_eq_projection]
  congr 1
  congr 1
  · by_cases h : [(j, false)] <+: w
    · simp [middleBasis, erase, eraseBasis, h, createBasis_eq_projection, List.drop_one]
    · simp [middleBasis, erase, eraseBasis, h]
  · simp [erase]


/-- The entire pair action is a compression of a sum of three pure prefix pieces. -/
theorem three_piece_compression (i j : α) (hij : i ≠ j) (w : Word α)
    (hw : FreeGroup.IsReduced w) :
    Finsupp.single (FreeGroup.reduce ((i, false) :: (j, true) :: w)) (1 : ℂ) =
      reducedProjection (
        pureCreate [(i, false), (j, true)] (Finsupp.single w 1) +
        pureCreate [(i, false)] (erase [(j, false)] (Finsupp.single w 1)) +
        erase [(j, false), (i, true)] (Finsupp.single w 1)) := by
  rw [map_add, map_add, three_piece_fock i j hij w hw]
  congr 1
  simpa [erase] using (reducedProjection_eraseBasis [(j, false), (i, true)] w hw).symm


/-- Linear extension of the reduced left action by `g_i⁻¹ g_j`. -/
def pairActionMap (i j : α) : (Word α →₀ ℂ) →ₗ[ℂ] (Word α →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun w =>
    Finsupp.single (FreeGroup.reduce ((i, false) :: (j, true) :: w)) 1)

/-- The three-piece identity as an equality of linear maps on the full list Fock space. -/
theorem three_piece_linearMap (i j : α) (hij : i ≠ j) :
    (pairActionMap i j).comp reducedProjection =
      reducedProjection.comp
        ((pureCreate [(i, false), (j, true)] +
          (pureCreate [(i, false)]).comp (erase [(j, false)]) +
          erase [(j, false), (i, true)]).comp reducedProjection) := by
  classical
  apply Finsupp.lhom_ext
  intro w c
  have hs : Finsupp.single w c = c • Finsupp.single w (1 : ℂ) := by simp
  rw [hs]
  simp only [map_smul]
  congr 1
  by_cases hw : FreeGroup.IsReduced w
  · have hQ : reducedProjection (Finsupp.single w (1 : ℂ)) = Finsupp.single w 1 := by
      simp [reducedProjection, hw]
    simp only [LinearMap.comp_apply, hQ, LinearMap.add_apply]
    simpa only [pairActionMap, Finsupp.linearCombination_single, one_smul] using
      three_piece_compression i j hij w hw
  · simp [LinearMap.comp_apply, reducedProjection, hw]

/-- Prefixing a fixed word is injective. -/
theorem prefix_injective (v : Word α) : Function.Injective (fun w : Word α => v ++ w) := by
  intro w₁ w₂ h
  exact List.append_cancel_left h

/-- Distinct prefixes of equal length have disjoint sets of extensions. -/
theorem prefix_ranges_disjoint (v₁ v₂ : Word α) (hlen : v₁.length = v₂.length)
    (hne : v₁ ≠ v₂) :
    Disjoint (Set.range fun w : Word α => v₁ ++ w)
      (Set.range fun w : Word α => v₂ ++ w) := by
  rw [Set.disjoint_left]
  rintro z ⟨w₁, rfl⟩ ⟨w₂, h⟩
  apply hne
  have he := congrArg (List.take v₁.length) h
  rw [List.take_left' hlen.symm, List.take_left] at he
  exact he.symm

/-- A fixed-length, injective family of prefixes gives an injective
prefix-and-suffix parametrization. This is the orthogonality fact used in
coefficient-matrix norm estimates on the full list Fock space. -/
theorem prefix_family_injective {ι : Type*} (v : ι → Word α) (hv : Function.Injective v)
    (hlen : ∀ i j, (v i).length = (v j).length) :
    Function.Injective (fun iw : ι × Word α => v iw.1 ++ iw.2) := by
  rintro ⟨i, w⟩ ⟨j, z⟩ h
  have hp : v i = v j := by
    have he := congrArg (List.take (v i).length) h
    rw [List.take_left, List.take_left' (hlen j i)] at he
    exact he
  have hij : i = j := hv hp
  subst j
  have hwz : w = z := List.append_cancel_left h
  subst z
  rfl

end
end PrefixOperators
end AdderTrace



/-! Source component: TupleAction.lean -/

open scoped BigOperators
open AdderTrace.PrefixOperators

namespace ExplicitFilter

noncomputable section

abbrev TupleWord (ι α : Type*) := ι → Word α

variable {ι α : Type*} [DecidableEq α]

/-- Coordinatewise reduced action of the pairs of free generators. -/
def tupleWordAction (I J : ι → α) (w : TupleWord ι α) : TupleWord ι α :=
  fun t => FreeGroup.reduce ((I t, false) :: (J t, true) :: w t)

/-- The genuine left action of a tensor generator pair, linearly extended. -/
def tupleActionMap (I J : ι → α) :
    (TupleWord ι α →₀ ℂ) →ₗ[ℂ] (TupleWord ι α →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun w => Finsupp.single (tupleWordAction I J w) 1)

/-- The same action with an arbitrary untouched coordinate. -/
def tupleActionMapWithSuffix {ζ : Type*} (I J : ι → α) :
    ((TupleWord ι α × ζ) →₀ ℂ) →ₗ[ℂ] ((TupleWord ι α × ζ) →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun wz =>
    Finsupp.single (tupleWordAction I J wz.1, wz.2) 1)

variable [Fintype ι] [DecidableEq ι] [Fintype α]

/-- The tensor free polynomial acting on finitely supported word tuples. -/
def tupleConvolution (W : (ι → α) → (ι → α) → ℂ)
    (f : TupleWord ι α →₀ ℂ) : TupleWord ι α →₀ ℂ :=
  ∑ I, ∑ J, W I J • tupleActionMap I J f

/-- Tensor convolution amplified by an arbitrary passive label set. -/
def tupleConvolutionWithSuffix {ζ : Type*}
    (W : (ι → α) → (ι → α) → ℂ)
    (f : (TupleWord ι α × ζ) →₀ ℂ) : (TupleWord ι α × ζ) →₀ ℂ :=
  ∑ I, ∑ J, W I J • tupleActionMapWithSuffix I J f

end
end ExplicitFilter


/-! Source component: SupportSlices.lean -/

open scoped BigOperators

namespace ExplicitFilter
noncomputable section

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

def diffSupport (I J : ι → α) : Finset ι := Finset.univ.filter (fun t => I t ≠ J t)

def coefficientSlice (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι) (I J : ι → α) : ℂ :=
  if diffSupport I J = S then W I J else 0

def mergeIndex (S : Finset ι) (a : S → α) (t : {i // i ∉ S} → α) : ι → α :=
  (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => α)).symm (a,t)

@[simp] theorem mergeIndex_mem (S : Finset ι) (a : S → α)
    (t : {i // i ∉ S} → α) (i : S) : mergeIndex S a t i = a i := by
  simp [mergeIndex, Equiv.piEquivPiSubtypeProd]

@[simp] theorem mergeIndex_notmem (S : Finset ι) (a : S → α)
    (t : {i // i ∉ S} → α) (i : {i // i ∉ S}) : mergeIndex S a t i = t i := by
  simp [mergeIndex, Equiv.piEquivPiSubtypeProd, i.property]

def collapsedSlice (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι)
    (i j : S → α) : ℂ :=
  ∑ t : {i // i ∉ S} → α, coefficientSlice W S (mergeIndex S i t) (mergeIndex S j t)

theorem collapsedSlice_zero (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι)
    (i j : S → α) (h : ∃ t, i t = j t) : collapsedSlice W S i j = 0 := by
  obtain ⟨u, hu⟩ := h
  unfold collapsedSlice
  apply Finset.sum_eq_zero
  intro t _
  have hne : diffSupport (mergeIndex S i t) (mergeIndex S j t) ≠ S := by
    intro he
    have hm : (u : ι) ∈ diffSupport (mergeIndex S i t) (mergeIndex S j t) := by
      rw [he]
      exact u.property
    simpa [diffSupport, hu] using hm
  simp [coefficientSlice, hne]

theorem sum_comp_injective_le {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X → Y) (he : Function.Injective e) (f : Y → ℝ) (hf : ∀ y, 0 ≤ f y) :
    (∑ x, f (e x)) ≤ ∑ y, f y := by
  classical
  calc
    (∑ x, f (e x)) = ∑ y ∈ Finset.univ.image e, f y :=
      (Finset.sum_image (fun x _ y _ h => he h)).symm
    _ ≤ ∑ y, f y := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun y _ _ => hf y)

theorem mergePair_injective (S : Finset ι) : Function.Injective
    (fun p : ((S → α) × (S → α)) × ({i // i ∉ S} → α) =>
      (mergeIndex S p.1.1 p.2, mergeIndex S p.1.2 p.2)) := by
  intro p q h
  have hi := congrArg Prod.fst h
  have hj := congrArg Prod.snd h
  apply Prod.ext
  · apply Prod.ext
    · funext u
      simpa using congrFun hi (u : ι)
    · funext u
      simpa using congrFun hj (u : ι)
  · funext u
    simpa using congrFun hi (u : ι)

theorem collapsedSlice_energy_le (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι) :
    (∑ i, ∑ j, ‖collapsedSlice W S i j‖ ^ 2) ≤
      (Fintype.card α : ℝ) ^ (Fintype.card ι - S.card) *
        ∑ I, ∑ J, ‖coefficientSlice W S I J‖ ^ 2 := by
  let T := {i // i ∉ S} → α
  have hcs : (∑ i, ∑ j, ‖collapsedSlice W S i j‖ ^ 2) ≤
      (Fintype.card T : ℝ) *
        ∑ i, ∑ j, ∑ t : T,
          ‖coefficientSlice W S (mergeIndex S i t) (mergeIndex S j t)‖ ^ 2 := by
    simp only [collapsedSlice, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simpa [Finset.mul_sum] using norm_sum_sq_le_card_sum Finset.univ
      (fun t : T => coefficientSlice W S (mergeIndex S i t) (mergeIndex S j t))
  have he := sum_comp_injective_le
    (fun p : ((S → α) × (S → α)) × T =>
      (mergeIndex S p.1.1 p.2, mergeIndex S p.1.2 p.2))
    (mergePair_injective S)
    (fun p : (ι → α) × (ι → α) => ‖coefficientSlice W S p.1 p.2‖ ^ 2)
    (fun _ => sq_nonneg _)
  simp only [Fintype.sum_prod_type] at he
  have hcard : (Fintype.card T : ℝ) =
      (Fintype.card α : ℝ) ^ (Fintype.card ι - S.card) := by
    simp [T, Fintype.card_fun, Fintype.card_subtype_compl]
  exact hcs.trans (by rw [hcard]; exact mul_le_mul_of_nonneg_left he (by positivity))

theorem diffSupport_eq_empty (I J : ι → α) : diffSupport I J = ∅ ↔ I = J := by
  constructor
  · intro h
    funext t
    by_contra hne
    have : t ∈ diffSupport I J := by simp [diffSupport, hne]
    simpa [h] using this
  · rintro rfl
    simp [diffSupport]

def supportFamily (ι : Type*) [Fintype ι] [DecidableEq ι] : Finset (Finset ι) :=
  Finset.univ.powerset.erase ∅

@[simp] theorem mem_supportFamily (S : Finset ι) : S ∈ supportFamily ι ↔ S.Nonempty := by
  simp [supportFamily, Finset.nonempty_iff_ne_empty]

theorem sum_coefficientSlice (W : (ι → α) → (ι → α) → ℂ)
    (hW : ∀ I, W I I = 0) (I J : ι → α) :
    (∑ S ∈ supportFamily ι, coefficientSlice W S I J) = W I J := by
  classical
  by_cases h : I = J
  · subst J
    simp [coefficientSlice, hW]
  · have hm : diffSupport I J ∈ supportFamily ι := by
      rw [mem_supportFamily, Finset.nonempty_iff_ne_empty]
      exact fun he => h ((diffSupport_eq_empty I J).mp he)
    simp [coefficientSlice, hm]

theorem sum_coefficientSlice_energy (W : (ι → α) → (ι → α) → ℂ)
    (hW : ∀ I, W I I = 0) :
    (∑ S ∈ supportFamily ι, ∑ I, ∑ J, ‖coefficientSlice W S I J‖ ^ 2) =
      ∑ I, ∑ J, ‖W I J‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  by_cases h : I = J
  · subst J
    simp [coefficientSlice, hW]
  · have hm : diffSupport I J ∈ supportFamily ι := by
      rw [mem_supportFamily, Finset.nonempty_iff_ne_empty]
      exact fun he => h ((diffSupport_eq_empty I J).mp he)
    have hv (S : Finset ι) : ‖coefficientSlice W S I J‖ ^ 2 =
        if diffSupport I J = S then ‖W I J‖ ^ 2 else 0 := by
      by_cases hS : diffSupport I J = S <;> simp [coefficientSlice, hS]
    simp_rw [hv]
    simp [hm]

end
end ExplicitFilter


/-! Source component: SupportCoefficientSum.lean -/

open scoped BigOperators

namespace ExplicitFilter
noncomputable section

variable {ι α E : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
  [AddCommMonoid E] [Module ℂ E]

/-- Splitting a generator tuple into its active and passive labels reindexes a finite sum. -/
theorem sum_mergeIndex (S : Finset ι) (F : (ι → α) → E) :
    (∑ I, F I) = ∑ i : S → α, ∑ t : {i // i ∉ S} → α, F (mergeIndex S i t) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => α)
  simpa only [Fintype.sum_prod_type] using (Equiv.sum_comp e.symm F).symm

/-- A coefficient with different passive labels cannot belong to the support slice. -/
theorem coefficientSlice_merge_zero (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι)
    (i j : S → α) (t u : {i // i ∉ S} → α) (htu : t ≠ u) :
    coefficientSlice W S (mergeIndex S i t) (mergeIndex S j u) = 0 := by
  have hs : diffSupport (mergeIndex S i t) (mergeIndex S j u) ≠ S := by
    intro he
    apply htu
    funext v
    by_contra hne
    have hm : (v : ι) ∈ diffSupport (mergeIndex S i t) (mergeIndex S j u) := by
      simp [diffSupport, hne]
    rw [he] at hm
    exact v.property hm
  simp [coefficientSlice, hs]

/-- Summing the support-slice coefficients over the common passive labels
is exactly the collapsed coefficient array. -/
theorem sum_slice_smul (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι)
    (B : (S → α) → (S → α) → E) :
    (∑ I, ∑ J, coefficientSlice W S I J •
      B (fun t : S => I t) (fun t : S => J t)) =
    ∑ i, ∑ j, collapsedSlice W S i j • B i j := by
  classical
  rw [sum_mergeIndex S]
  simp_rw [sum_mergeIndex S]
  simp only [mergeIndex_mem]
  have hu (i j : S → α) (t : {i // i ∉ S} → α) :
      (∑ u : {i // i ∉ S} → α,
        coefficientSlice W S (mergeIndex S i t) (mergeIndex S j u) • B i j) =
      coefficientSlice W S (mergeIndex S i t) (mergeIndex S j t) • B i j := by
    apply Finset.sum_eq_single t
    · intro u _ hut
      rw [coefficientSlice_merge_zero W S i j t u (Ne.symm hut), zero_smul]
    · simp
  simp_rw [hu]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp only [collapsedSlice, Finset.sum_smul]

end
end ExplicitFilter


/-! Source component: PrefixMatrices.lean -/

open scoped BigOperators
open AdderTrace.PrefixOperators

namespace ExplicitFilter
noncomputable section

variable {α : Type*} [DecidableEq α]

/-- The injective parametrization by a prefix and an arbitrary suffix. -/
def familyPrefixEmbedding {ι : Type*} (v : ι → Word α) (hv : Function.Injective v)
    (hlen : ∀ i j, (v i).length = (v j).length) : (ι × Word α) ↪ Word α :=
  ⟨fun iw => v iw.1 ++ iw.2, prefix_family_injective v hv hlen⟩

/-- Pure prefix creation is the usual relabeling map. -/
theorem pureCreate_eq_lmapDomain (v : Word α) :
    pureCreate v = Finsupp.lmapDomain ℂ ℂ (fun w => v ++ w) := by
  apply Finsupp.lhom_ext
  intro w c
  simp [pureCreate]

/-- The removal basis kernel is an elementary prefix indicator. -/
theorem eraseBasis_apply_indicator (v y w : Word α) :
    eraseBasis v y w = if v ++ w = y then (1 : ℂ) else 0 := by
  classical
  by_cases h : v ++ w = y
  · subst y
    simp [eraseBasis]
  · by_cases hp : v <+: y
    · have hn : w ≠ y.drop v.length := by
        intro he
        apply h
        rw [he]
        exact List.prefix_iff_eq_append.mp hp
      simp [eraseBasis, hp, h, Finsupp.single_eq_of_ne hn]
    · simp [eraseBasis, hp, h]

/-- Pure removal reads the coefficient at the prefixed word. -/
theorem erase_eq_lcomapDomain (v : Word α) :
    erase v = Finsupp.lcomapDomain (R := ℂ) (M := ℂ)
      (fun w => v ++ w) (prefix_injective v) := by
  classical
  apply Finsupp.lhom_ext
  intro y c
  ext w
  simp only [erase, Finsupp.linearCombination_single, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.lcomapDomain, LinearMap.coe_mk, AddHom.coe_mk,
    Finsupp.comapDomain_apply, eraseBasis_apply_indicator]
  by_cases h : v ++ w = y <;> simp [h, Finsupp.single_apply, eq_comm]

@[simp] theorem erase_apply (v : Word α) (f : Word α →₀ ℂ) (w : Word α) :
    erase v f w = f (v ++ w) := by
  rw [erase_eq_lcomapDomain]
  rfl

/-- Evaluating a fixed-length prefix family picks out exactly its matching prefix. -/
theorem pureCreate_apply_family {ι : Type*} [DecidableEq ι]
    (v : ι → Word α) (hv : Function.Injective v)
    (hlen : ∀ i j, (v i).length = (v j).length)
    (i j : ι) (f : Word α →₀ ℂ) (w : Word α) :
    pureCreate (v i) f (v j ++ w) = if i = j then f w else 0 := by
  rw [pureCreate_eq_lmapDomain, Finsupp.lmapDomain_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    exact Finsupp.mapDomain_apply (prefix_injective (v i)) f w
  · simp only [hij, ite_false]
    apply Finsupp.mapDomain_notin_range
    rintro ⟨z, hz⟩
    have he := prefix_family_injective v hv hlen (a₁ := (i, z)) (a₂ := (j, w)) hz
    exact hij (congrArg Prod.fst he)

/-- A finite coefficient matrix between prefix creation and removal operators
is exactly an embedded suffix-wise matrix action. -/
theorem prefix_matrix_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → Word α) (hv : Function.Injective v)
    (hlen : ∀ i j, (v i).length = (v j).length)
    (u : κ → Word α) (hu : Function.Injective u)
    (ulen : ∀ i j, (u i).length = (u j).length)
    (C : ι → κ → ℂ) (f : Word α →₀ ℂ) :
    (∑ i, ∑ j, C i j • pureCreate (v i) (erase (u j) f)) =
      Finsupp.embDomain (familyPrefixEmbedding v hv hlen)
        (blockMatrix C (Finsupp.comapDomain (familyPrefixEmbedding u hu ulen) f
          (familyPrefixEmbedding u hu ulen).injective.injOn)) := by
  classical
  ext w
  by_cases hw : w ∈ Set.range (familyPrefixEmbedding v hv hlen)
  · rcases hw with ⟨⟨i, z⟩, rfl⟩
    rw [Finsupp.embDomain_apply, blockMatrix_apply]
    simp [familyPrefixEmbedding, pureCreate_apply_family v hv hlen,
      Finsupp.finset_sum_apply, Finsupp.smul_apply]
  · rw [Finsupp.embDomain_notin_range _ _ _ hw]
    simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hz : pureCreate (v i) (erase (u j) f) w = 0 := by
      rw [pureCreate_eq_lmapDomain, Finsupp.lmapDomain_apply]
      apply Finsupp.mapDomain_notin_range
      rintro ⟨z, hz⟩
      exact hw ⟨(i, z), hz⟩
    simp [hz]

/-- Frobenius bound for any coefficient matrix between two fixed-length
families of pure prefix operators. -/
theorem l2Sq_prefix_sum_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → Word α) (hv : Function.Injective v)
    (hlen : ∀ i j, (v i).length = (v j).length)
    (u : κ → Word α) (hu : Function.Injective u)
    (ulen : ∀ i j, (u i).length = (u j).length)
    (C : ι → κ → ℂ) (f : Word α →₀ ℂ) :
    l2Sq (∑ i, ∑ j, C i j • pureCreate (v i) (erase (u j) f)) ≤
      (∑ i, ∑ j, ‖C i j‖ ^ 2) * l2Sq f := by
  rw [prefix_matrix_eq v hv hlen u hu ulen C f]
  exact l2Sq_prefix_matrix_le _ _ _ _

end
end ExplicitFilter


/-! Source component: PrefixProjection.lean -/

open scoped BigOperators
open AdderTrace.PrefixOperators

namespace ExplicitFilter
noncomputable section
attribute [local instance] Classical.propDecidable

variable {α : Type*} [DecidableEq α]

/-- The formal reduced-word projection is precisely a coordinate filter. -/
theorem reducedProjection_eq_filter (f : Word α →₀ ℂ) :
    reducedProjection f = f.filter FreeGroup.IsReduced := by
  classical
  let P : (Word α →₀ ℂ) →ₗ[ℂ] (Word α →₀ ℂ) :=
    { toFun := fun f => f.filter FreeGroup.IsReduced
      map_add' := fun _ _ => Finsupp.filter_add
      map_smul' := fun _ _ => Finsupp.filter_smul }
  have hP : reducedProjection = P := by
    apply Finsupp.lhom_ext
    intro w c
    by_cases hw : FreeGroup.IsReduced w
    · simp [reducedProjection, P, hw, Finsupp.filter_single_of_pos _ hw]
    · simp [reducedProjection, P, hw, Finsupp.filter_single_of_neg _ hw]
  exact congrArg (fun T : (Word α →₀ ℂ) →ₗ[ℂ] (Word α →₀ ℂ) => T f) hP

/-- Compression to the reduced-word subspace is a contraction. -/
theorem l2Sq_reducedProjection_le (f : Word α →₀ ℂ) :
    l2Sq (reducedProjection f) ≤ l2Sq f := by
  rw [reducedProjection_eq_filter]
  exact l2Sq_filter_le _ _

/-- Three cancellation pieces combine with the square of the factor three. -/
theorem l2Sq_add_three_le {β : Type*} (f g h : β →₀ ℂ) :
    l2Sq (f + g + h) ≤ 3 * (l2Sq f + l2Sq g + l2Sq h) := by
  have he := l2Sq_sum_le (Finset.univ : Finset (Fin 3)) ![f, g, h]
  simpa [Fin.sum_univ_three, add_assoc] using he

end
end ExplicitFilter


/-! Source component: TensorPrefixMatrices.lean -/

/-!
Prefix matrix estimates on arbitrary products of reduced-word Fock spaces.
The definitions below are actual finitely supported linear maps; no norm estimate
or decomposition is assumed in this module.
-/

open scoped BigOperators Classical
open AdderTrace.PrefixOperators

namespace ExplicitFilter
noncomputable section

abbrev TensorWord (α γ : Type*) := γ → Word α
abbrev TensorState (α γ ζ : Type*) := TensorWord α γ × ζ

variable {α γ ζ : Type*}

/-- Coordinatewise prefixing on active coordinates, preserving a passive register. -/
def tensorAppend (v : TensorWord α γ) (w : TensorState α γ ζ) : TensorState α γ ζ :=
  (fun t => v t ++ w.1 t, w.2)

@[simp] theorem tensorAppend_apply (v : TensorWord α γ) (w : TensorState α γ ζ) (t : γ) :
    (tensorAppend v w).1 t = v t ++ w.1 t := rfl

@[simp] theorem tensorAppend_snd (v : TensorWord α γ) (w : TensorState α γ ζ) :
    (tensorAppend v w).2 = w.2 := rfl

/-- Prefixing the same word tuple is injective. -/
theorem tensorAppend_injective (v : TensorWord α γ) :
    Function.Injective (tensorAppend (ζ := ζ) v) := by
  intro w z h
  apply Prod.ext
  · funext t
    exact List.append_cancel_left (congrArg (fun x => x.1 t) h)
  · have hs := congrArg (fun x : TensorState α γ ζ => x.2) h
    exact hs

/-- Pure prefix creation, amplified by an arbitrary passive register. -/
def tensorPureCreate (v : TensorWord α γ) :
    (TensorState α γ ζ →₀ ℂ) →ₗ[ℂ] (TensorState α γ ζ →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (tensorAppend v)

/-- Pure prefix removal, amplified by an arbitrary passive register. -/
def tensorErase (v : TensorWord α γ) :
    (TensorState α γ ζ →₀ ℂ) →ₗ[ℂ] (TensorState α γ ζ →₀ ℂ) :=
  Finsupp.lcomapDomain (tensorAppend v) (tensorAppend_injective v)

@[simp] theorem tensorErase_apply (v : TensorWord α γ) (w : TensorState α γ ζ)
    (f : TensorState α γ ζ →₀ ℂ) :
    tensorErase v f w = f (tensorAppend v w) := rfl

@[simp] theorem tensorPureCreate_single (v : TensorWord α γ) (w : TensorState α γ ζ) (c : ℂ) :
    tensorPureCreate v (Finsupp.single w c) = Finsupp.single (tensorAppend v w) c := by
  simp [tensorPureCreate]

/-- Joint prefix-index and suffix parametrization is injective when each
coordinate has a prescribed prefix length. -/
theorem tensor_prefix_family_injective {ι : Type*} (v : ι → TensorWord α γ)
    (hv : Function.Injective v)
    (hlen : ∀ i j t, (v i t).length = (v j t).length) :
    Function.Injective (fun iw : ι × TensorState α γ ζ => tensorAppend (v iw.1) iw.2) := by
  rintro ⟨i, w⟩ ⟨j, z⟩ h
  have hp : v i = v j := by
    funext t
    have he := congrArg (fun f : TensorState α γ ζ => (f.1 t).take (v i t).length) h
    change (v i t ++ w.1 t).take (v i t).length =
      (v j t ++ z.1 t).take (v i t).length at he
    rw [List.take_left, List.take_left' (hlen j i t)] at he
    exact he
  have hij := hv hp
  subst j
  have hwz : w = z := tensorAppend_injective (v i) h
  subst z
  rfl

/-- Embedding of a fixed-length tuple-prefix family and a common suffix tuple. -/
def tensorFamilyPrefixEmbedding {ι : Type*} (v : ι → TensorWord α γ)
    (hv : Function.Injective v)
    (hlen : ∀ i j t, (v i t).length = (v j t).length) :
    (ι × TensorState α γ ζ) ↪ TensorState α γ ζ :=
  ⟨fun iw => tensorAppend (v iw.1) iw.2, tensor_prefix_family_injective v hv hlen⟩

/-- Prefix creation has orthogonal output ranges for distinct members of a
fixed-length tuple-prefix family. -/
theorem tensorPureCreate_apply_family {ι : Type*} [DecidableEq ι]
    (v : ι → TensorWord α γ) (hv : Function.Injective v)
    (hlen : ∀ i j t, (v i t).length = (v j t).length)
    (i j : ι) (f : TensorState α γ ζ →₀ ℂ) (w : TensorState α γ ζ) :
    tensorPureCreate (v i) f (tensorAppend (v j) w) = if i = j then f w else 0 := by
  change Finsupp.mapDomain (tensorAppend (v i)) f (tensorAppend (v j) w) = _
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    exact Finsupp.mapDomain_apply (tensorAppend_injective (v i)) f w
  · simp only [hij, ite_false]
    apply Finsupp.mapDomain_notin_range
    rintro ⟨z, hz⟩
    have he := tensor_prefix_family_injective v hv hlen
      (a₁ := (i, z)) (a₂ := (j, w)) hz
    exact hij (congrArg Prod.fst he)

/-- The actual tuple-prefix matrix equals a coefficient matrix tensored with
an identity on arbitrary suffixes, between two coordinate embeddings. -/
theorem tensor_prefix_matrix_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → TensorWord α γ) (hv : Function.Injective v)
    (hlen : ∀ i j t, (v i t).length = (v j t).length)
    (u : κ → TensorWord α γ) (hu : Function.Injective u)
    (ulen : ∀ i j t, (u i t).length = (u j t).length)
    (C : ι → κ → ℂ) (f : TensorState α γ ζ →₀ ℂ) :
    (∑ i, ∑ j, C i j • tensorPureCreate (v i) (tensorErase (u j) f)) =
      Finsupp.embDomain (tensorFamilyPrefixEmbedding v hv hlen)
        (blockMatrix C (Finsupp.comapDomain (tensorFamilyPrefixEmbedding u hu ulen) f
          (tensorFamilyPrefixEmbedding u hu ulen).injective.injOn)) := by
  classical
  ext w
  by_cases hw : w ∈ Set.range (tensorFamilyPrefixEmbedding v hv hlen)
  · rcases hw with ⟨⟨i, z⟩, rfl⟩
    rw [Finsupp.embDomain_apply, blockMatrix_apply]
    simp [tensorFamilyPrefixEmbedding, tensorPureCreate_apply_family v hv hlen,
      Finsupp.finset_sum_apply, Finsupp.smul_apply]
  · rw [Finsupp.embDomain_notin_range _ _ _ hw]
    simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hz : tensorPureCreate (v i) (tensorErase (u j) f) w = 0 := by
      change Finsupp.mapDomain (tensorAppend (v i)) (tensorErase (u j) f) w = 0
      apply Finsupp.mapDomain_notin_range
      rintro ⟨z, hz⟩
      exact hw ⟨(i, z), hz⟩
    simp [hz]

/-- Each prescribed tuple cancellation pattern has norm at most its
coefficient Frobenius norm, for every number of coordinates. -/
theorem l2Sq_tensor_prefix_sum_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → TensorWord α γ) (hv : Function.Injective v)
    (hlen : ∀ i j t, (v i t).length = (v j t).length)
    (u : κ → TensorWord α γ) (hu : Function.Injective u)
    (ulen : ∀ i j t, (u i t).length = (u j t).length)
    (C : ι → κ → ℂ) (f : TensorState α γ ζ →₀ ℂ) :
    l2Sq (∑ i, ∑ j, C i j • tensorPureCreate (v i) (tensorErase (u j) f)) ≤
      (∑ i, ∑ j, ‖C i j‖ ^ 2) * l2Sq f := by
  rw [tensor_prefix_matrix_eq v hv hlen u hu ulen C f]
  exact l2Sq_prefix_matrix_le _ _ _ _

/-- Coordinate projection onto tuples that are reduced in every coordinate. -/
def tensorProjection : (TensorState α γ ζ →₀ ℂ) →ₗ[ℂ] (TensorState α γ ζ →₀ ℂ) := by
  classical
  exact {
    toFun := fun f => f.filter (fun w => ∀ t, FreeGroup.IsReduced (w.1 t))
    map_add' := fun _ _ => Finsupp.filter_add
    map_smul' := fun _ _ => Finsupp.filter_smul }

@[simp] theorem tensorProjection_apply (f : TensorState α γ ζ →₀ ℂ) (w : TensorState α γ ζ) :
    tensorProjection f w = if ∀ t, FreeGroup.IsReduced (w.1 t) then f w else 0 := by
  classical
  rfl

/-- Reduced-word compression is contractive. -/
theorem l2Sq_tensorProjection_le (f : TensorState α γ ζ →₀ ℂ) :
    l2Sq (tensorProjection f) ≤ l2Sq f := by
  classical
  exact l2Sq_filter_le _ f

@[simp] theorem tensorProjection_single (w : TensorState α γ ζ) (c : ℂ)
    (hw : ∀ t, FreeGroup.IsReduced (w.1 t)) :
    tensorProjection (Finsupp.single w c) = Finsupp.single w c := by
  classical
  exact Finsupp.filter_single_of_pos _ hw

@[simp] theorem tensorProjection_idempotent (f : TensorState α γ ζ →₀ ℂ) :
    tensorProjection (tensorProjection f) = tensorProjection f := by
  classical
  ext w
  change (if ∀ t, FreeGroup.IsReduced (w.1 t) then
    (if ∀ t, FreeGroup.IsReduced (w.1 t) then f w else 0) else 0) =
    (if ∀ t, FreeGroup.IsReduced (w.1 t) then f w else 0)
  split_ifs <;> rfl

/-- Reduced support is exactly the fixed subspace of the tuple projection. -/
theorem tensorProjection_eq_self_iff (f : TensorState α γ ζ →₀ ℂ) :
    tensorProjection f = f ↔
      ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w.1 t) := by
  classical
  change f.filter (fun w => ∀ t, FreeGroup.IsReduced (w.1 t)) = f ↔ _
  rw [Finsupp.filter_eq_self_iff]
  simp only [Finsupp.mem_support_iff]

/-- Any vector supported on reduced tuples is unchanged by compression. -/
theorem tensorProjection_eq_self (f : TensorState α γ ζ →₀ ℂ)
    (hf : ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w.1 t)) :
    tensorProjection f = f := (tensorProjection_eq_self_iff f).2 hf

/-- Compressing either or both sides preserves the tuple-prefix estimate. -/
theorem l2Sq_compressed_tensor_prefix_sum_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → TensorWord α γ) (hv : Function.Injective v)
    (hlen : ∀ i j t, (v i t).length = (v j t).length)
    (u : κ → TensorWord α γ) (hu : Function.Injective u)
    (ulen : ∀ i j t, (u i t).length = (u j t).length)
    (C : ι → κ → ℂ) (f : TensorState α γ ζ →₀ ℂ) :
    l2Sq (tensorProjection (∑ i, ∑ j, C i j •
      tensorPureCreate (v i) (tensorErase (u j) (tensorProjection f)))) ≤
      (∑ i, ∑ j, ‖C i j‖ ^ 2) * l2Sq f := by
  calc
    _ ≤ l2Sq (∑ i, ∑ j, C i j •
        tensorPureCreate (v i) (tensorErase (u j) (tensorProjection f))) :=
      l2Sq_tensorProjection_le _
    _ ≤ (∑ i, ∑ j, ‖C i j‖ ^ 2) * l2Sq (tensorProjection f) :=
      l2Sq_tensor_prefix_sum_le v hv hlen u hu ulen C _
    _ ≤ _ := mul_le_mul_of_nonneg_left (l2Sq_tensorProjection_le f) (by positivity)

end
end ExplicitFilter


/-! Source component: SupportAction.lean -/

open scoped BigOperators Classical
open AdderTrace.PrefixOperators

namespace ExplicitFilter
noncomputable section

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Split active and inactive word coordinates along a support set. -/
def splitWords (S : Finset ι) : TupleWord ι α ≃
    (TupleWord S α × TupleWord {i // i ∉ S} α) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Word α)

@[simp] theorem splitWords_fst (S : Finset ι) (w : TupleWord ι α) (t : S) :
    (splitWords S w).1 t = w t := rfl

@[simp] theorem splitWords_snd (S : Finset ι) (w : TupleWord ι α) (t : {i // i ∉ S}) :
    (splitWords S w).2 t = w t := rfl

/-- Relabel the word basis by the active/passive split. -/
def splitWordMap (S : Finset ι) : (TupleWord ι α →₀ ℂ) →ₗ[ℂ]
    ((TupleWord S α × TupleWord {i // i ∉ S} α) →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (splitWords S)

@[simp] theorem splitWordMap_single (S : Finset ι) (w : TupleWord ι α) (c : ℂ) :
    splitWordMap S (Finsupp.single w c) = Finsupp.single (splitWords S w) c := by
  simp [splitWordMap]

theorem splitWordMap_eq_embDomain (S : Finset ι) (f : TupleWord ι α →₀ ℂ) :
    splitWordMap S f = Finsupp.embDomain (splitWords S).toEmbedding f := by
  exact (Finsupp.embDomain_eq_mapDomain (splitWords S).toEmbedding f).symm

@[simp] theorem l2Sq_splitWordMap (S : Finset ι) (f : TupleWord ι α →₀ ℂ) :
    l2Sq (splitWordMap S f) = l2Sq f := by
  rw [splitWordMap_eq_embDomain, l2Sq_embDomain]

/-- An equal generator pair cancels on every reduced word. -/
theorem reduce_same_pair (i : α) (w : Word α) (hw : FreeGroup.IsReduced w) :
    FreeGroup.reduce ((i, false) :: (i, true) :: w) = w := by
  have h : FreeGroup.reduce ((i, false) :: (i, true) :: w) = FreeGroup.reduce w :=
    FreeGroup.reduce.Step.eq (FreeGroup.Red.Step.cons_not (x := i) (b := false))
  exact h.trans hw.reduce_eq

/-- Outside the difference support the generator labels coincide. -/
theorem equal_outside_diffSupport (S : Finset ι) (I J : ι → α)
    (hS : diffSupport I J = S) (t : {i // i ∉ S}) : I t = J t := by
  by_contra hne
  have ht : (t : ι) ∈ diffSupport I J := by simp [diffSupport, hne]
  rw [hS] at ht
  exact t.property ht

/-- A tensor pair acts trivially on inactive reduced coordinates. -/
theorem splitWords_action (S : Finset ι) (I J : ι → α)
    (hIJ : ∀ t : {i // i ∉ S}, I t = J t)
    (w : TupleWord ι α) (hw : ∀ t, FreeGroup.IsReduced (w t)) :
    splitWords S (tupleWordAction I J w) =
      (tupleWordAction (fun t : S => I t) (fun t : S => J t) (splitWords S w).1,
        (splitWords S w).2) := by
  apply Prod.ext
  · rfl
  · funext t
    change FreeGroup.reduce ((I t, false) :: (J t, true) :: w t) = w t
    rw [hIJ t]
    exact reduce_same_pair _ _ (hw t)

/-- Splitting the basis conjugates a supported tensor action to its active
coordinate action, amplified by the untouched inactive coordinates. -/
theorem splitWordMap_action (S : Finset ι) (I J : ι → α)
    (hIJ : ∀ t : {i // i ∉ S}, I t = J t)
    (f : TupleWord ι α →₀ ℂ)
    (hf : ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) :
    splitWordMap S (tupleActionMap I J f) =
      tupleActionMapWithSuffix (fun t : S => I t) (fun t : S => J t)
        (splitWordMap S f) := by
  unfold tupleActionMap tupleActionMapWithSuffix
  rw [Finsupp.apply_linearCombination]
  rw [splitWordMap_eq_embDomain, Finsupp.linearCombination_embDomain]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [Function.comp_apply, splitWordMap_single]
  rw [splitWords_action S I J hIJ w (hf w hw)]
  rfl

/-- The support restriction is exactly what is needed for the action conjugacy. -/
theorem splitWordMap_slice_pair (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι)
    (I J : ι → α) (f : TupleWord ι α →₀ ℂ)
    (hf : ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) :
    splitWordMap S (coefficientSlice W S I J • tupleActionMap I J f) =
      coefficientSlice W S I J •
        tupleActionMapWithSuffix (fun t : S => I t) (fun t : S => J t)
          (splitWordMap S f) := by
  by_cases hS : diffSupport I J = S
  · rw [map_smul, splitWordMap_action S I J (equal_outside_diffSupport S I J hS) f hf]
  · simp [coefficientSlice, hS]

/-- The complete support slice is conjugate to the collapsed active
coefficient matrix, acting with the inactive coordinates as a passive register. -/
theorem splitWordMap_slice_convolution (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι)
    (f : TupleWord ι α →₀ ℂ)
    (hf : ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) :
    splitWordMap S (tupleConvolution (coefficientSlice W S) f) =
      tupleConvolutionWithSuffix (collapsedSlice W S) (splitWordMap S f) := by
  simp only [tupleConvolution, map_sum]
  simp_rw [splitWordMap_slice_pair W S _ _ f hf]
  exact sum_slice_smul W S (fun i j => tupleActionMapWithSuffix i j (splitWordMap S f))

/-- Squared norms are unchanged by the concrete support-slice conjugacy. -/
theorem l2Sq_slice_convolution_eq (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι)
    (f : TupleWord ι α →₀ ℂ)
    (hf : ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) :
    l2Sq (tupleConvolution (coefficientSlice W S) f) =
      l2Sq (tupleConvolutionWithSuffix (collapsedSlice W S) (splitWordMap S f)) := by
  rw [← l2Sq_splitWordMap S (tupleConvolution (coefficientSlice W S) f),
    splitWordMap_slice_convolution W S f hf]

/-- A split of a reduced vector is reduced on the active coordinates. -/
theorem splitWordMap_support_reduced (S : Finset ι) (f : TupleWord ι α →₀ ℂ)
    (hf : ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) :
    ∀ w ∈ (splitWordMap S f).support, ∀ t, FreeGroup.IsReduced (w.1 t) := by
  intro w hw
  rw [splitWordMap_eq_embDomain, Finsupp.support_embDomain] at hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
  intro t
  exact hf v hv t

/-- The active-coordinate projection fixes the split of a reduced vector. -/
theorem tensorProjection_splitWordMap (S : Finset ι) (f : TupleWord ι α →₀ ℂ)
    (hf : ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) :
    tensorProjection (splitWordMap S f) = splitWordMap S f :=
  tensorProjection_eq_self _ (splitWordMap_support_reduced S f hf)

end
end ExplicitFilter


/-! Source component: WeightedL2.lean -/

open scoped BigOperators
namespace ExplicitFilter

/-- Weighted Cauchy--Schwarz for a sum of complex scalars. -/
theorem norm_sum_sq_le_weighted {ι : Type*} (s : Finset ι)
    (f : ι → ℂ) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, ‖f i‖ ^ 2 / w i := by
  classical
  by_cases hs : s.Nonempty
  · have hwpos : 0 < ∑ i ∈ s, w i := Finset.sum_pos hw hs
    have hcs := (div_le_iff₀ hwpos).mp
      (Finset.sq_sum_div_le_sum_sq_div s (fun i => ‖f i‖) hw)
    calc
      _ ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
      _ ≤ _ := by simpa [mul_comm] using hcs
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- Weighted Cauchy--Schwarz for finitely supported vectors. -/
theorem l2Sq_sum_le_weighted {α ι : Type*} (s : Finset ι)
    (f : ι → α →₀ ℂ) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) :
    l2Sq (∑ i ∈ s, f i) ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, l2Sq (f i) / w i := by
  classical
  let S := s.biUnion (fun i => (f i).support)
  have hmem (i : ι) (hi : i ∈ s) : (f i).support ⊆ S := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
  have hsub : (∑ i ∈ s, f i).support ⊆ S := by
    intro x hx
    by_contra hnot
    have hfzero : ∀ i ∈ s, f i x = 0 := by
      intro i hi
      apply Finsupp.notMem_support_iff.mp
      exact fun hx => hnot (hmem i hi hx)
    have hz : (∑ i ∈ s, f i) x = 0 := by
      simpa using Finset.sum_eq_zero hfzero
    exact Finsupp.mem_support_iff.mp hx hz
  rw [l2Sq_eq_sum _ S hsub]
  calc
    (∑ x ∈ S, ‖(∑ i ∈ s, f i) x‖ ^ 2) ≤
        ∑ x ∈ S, (∑ i ∈ s, w i) * ∑ i ∈ s, ‖f i x‖ ^ 2 / w i := by
      apply Finset.sum_le_sum
      intro x hx
      simpa using norm_sum_sq_le_weighted s (fun i => f i x) w hw
    _ = (∑ i ∈ s, w i) * ∑ i ∈ s, (∑ x ∈ S, ‖f i x‖ ^ 2) / w i := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← l2Sq_eq_sum (f i) S (hmem i hi)]

end ExplicitFilter


/-! Source component: SupportCombine.lean -/

open scoped BigOperators

namespace ExplicitFilter
noncomputable section

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

def sliceWeight (S : Finset ι) : ℝ :=
  (9 : ℝ) ^ S.card * (Fintype.card α : ℝ) ^ (Fintype.card ι - S.card)

theorem sliceWeight_pos [Nonempty α] (S : Finset ι) : 0 < sliceWeight (α := α) S := by
  unfold sliceWeight
  have : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  positivity

theorem sum_sliceWeights :
    (∑ S ∈ supportFamily ι, sliceWeight (α := α) S) =
      ((Fintype.card α : ℝ) + 9) ^ Fintype.card ι -
        (Fintype.card α : ℝ) ^ Fintype.card ι := by
  classical
  let M : ℝ := Fintype.card α
  have hfull : (∑ S ∈ (Finset.univ : Finset ι).powerset,
      (9 : ℝ) ^ S.card * M ^ (Fintype.card ι - S.card)) =
        (M + 9) ^ Fintype.card ι := by
    simpa [Finset.prod_const, Finset.card_sdiff, add_comm] using
      (Finset.prod_add (fun _ : ι => (9 : ℝ)) (fun _ => M) Finset.univ).symm
  have hzero : (∅ : Finset ι) ∈ (Finset.univ : Finset ι).powerset :=
    Finset.mem_powerset.mpr (Finset.empty_subset _)
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset ι).powerset)
    (f := fun S => (9 : ℝ) ^ S.card * M ^ (Fintype.card ι - S.card)) hzero
  simp only [Finset.card_empty, pow_zero, Nat.sub_zero, one_mul] at hsplit
  rw [hfull] at hsplit
  dsimp [supportFamily, sliceWeight]
  dsimp [M] at hsplit
  linarith

theorem tupleConvolution_eq_sum_slices
    (W : (ι → α) → (ι → α) → ℂ) (hW : ∀ I, W I I = 0)
    (f : TupleWord ι α →₀ ℂ) :
    tupleConvolution W f =
      ∑ S ∈ supportFamily ι, tupleConvolution (coefficientSlice W S) f := by
  unfold tupleConvolution
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Finset.sum_smul, sum_coefficientSlice W hW]

/-- The final weighted support assembly. The slice hypotheses are discharged
by the homogeneous tensor bound and the explicit coefficient collapse. -/
theorem full_convolution_bound_of_slices [Nonempty α]
    (W : (ι → α) → (ι → α) → ℂ) (hW : ∀ I, W I I = 0)
    (f : TupleWord ι α →₀ ℂ)
    (hslice : ∀ S ∈ supportFamily ι,
      l2Sq (tupleConvolution (coefficientSlice W S) f) ≤
        sliceWeight (α := α) S *
          (∑ I, ∑ J, ‖coefficientSlice W S I J‖ ^ 2) * l2Sq f) :
    l2Sq (tupleConvolution W f) ≤
      (((Fintype.card α : ℝ) + 9) ^ Fintype.card ι -
        (Fintype.card α : ℝ) ^ Fintype.card ι) *
          (∑ I, ∑ J, ‖W I J‖ ^ 2) * l2Sq f := by
  rw [tupleConvolution_eq_sum_slices W hW]
  have hp : ∀ S ∈ supportFamily ι, 0 < sliceWeight (α := α) S :=
    fun S _ => sliceWeight_pos S
  have hb := l2Sq_sum_le_weighted (supportFamily ι)
    (fun S => tupleConvolution (coefficientSlice W S) f)
    (sliceWeight (α := α)) hp
  have hdiv : (∑ S ∈ supportFamily ι,
      l2Sq (tupleConvolution (coefficientSlice W S) f) / sliceWeight (α := α) S) ≤
        ∑ S ∈ supportFamily ι,
          (∑ I, ∑ J, ‖coefficientSlice W S I J‖ ^ 2) * l2Sq f := by
    apply Finset.sum_le_sum
    intro S hS
    apply (div_le_iff₀ (hp S hS)).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hslice S hS
  have hn : 0 ≤ ∑ S ∈ supportFamily ι, sliceWeight (α := α) S :=
    Finset.sum_nonneg (fun S hS => le_of_lt (hp S hS))
  calc
    _ ≤ (∑ S ∈ supportFamily ι, sliceWeight (α := α) S) *
      ∑ S ∈ supportFamily ι,
        (∑ I, ∑ J, ‖coefficientSlice W S I J‖ ^ 2) * l2Sq f :=
      hb.trans (mul_le_mul_of_nonneg_left hdiv hn)
    _ = _ := by
      rw [sum_sliceWeights, ← Finset.sum_mul, sum_coefficientSlice_energy W hW]
      ring

end
end ExplicitFilter


/-! Source component: SupportBound.lean -/

open scoped BigOperators

namespace ExplicitFilter
noncomputable section

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Transport a bound for the collapsed active coefficient matrix back to
the original coordinates, inserting the exact inactive-coordinate count. -/
theorem slice_convolution_bound_of_collapsed
    (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι)
    (f : TupleWord ι α →₀ ℂ)
    (hf : ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t))
    (hactive : l2Sq (tupleConvolutionWithSuffix (collapsedSlice W S) (splitWordMap S f)) ≤
      (9 : ℝ) ^ Fintype.card S * (∑ i, ∑ j, ‖collapsedSlice W S i j‖ ^ 2) *
        l2Sq (splitWordMap S f)) :
    l2Sq (tupleConvolution (coefficientSlice W S) f) ≤
      sliceWeight (α := α) S * (∑ I, ∑ J, ‖coefficientSlice W S I J‖ ^ 2) * l2Sq f := by
  rw [l2Sq_slice_convolution_eq W S f hf]
  have henergy := collapsedSlice_energy_le W S
  have hnorm : 0 ≤ l2Sq f := l2Sq_nonneg f
  calc
    _ ≤ (9 : ℝ) ^ S.card * (∑ i, ∑ j, ‖collapsedSlice W S i j‖ ^ 2) * l2Sq f := by
      simpa using hactive
    _ ≤ (9 : ℝ) ^ S.card *
        ((Fintype.card α : ℝ) ^ (Fintype.card ι - S.card) *
          ∑ I, ∑ J, ‖coefficientSlice W S I J‖ ^ 2) * l2Sq f := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left henergy (by positivity)) hnorm
    _ = _ := by unfold sliceWeight; ring

end
end ExplicitFilter


/-! Source component: TensorKernel.lean -/

open scoped BigOperators
open AdderTrace.PrefixOperators

namespace ExplicitFilter
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A partial permutation given by one embedding followed by the inverse
of another has a zero-one kernel. -/
theorem map_comap_single_kernel {Ω Γ : Type*}
    (f g : Γ → Ω) (hf : Function.Injective f) (hg : Function.Injective g)
    (w y : Ω) :
    Finsupp.mapDomain f
      (Finsupp.comapDomain g (Finsupp.single w (1 : ℂ)) hg.injOn) y =
        if ∃ z, f z = y ∧ g z = w then (1 : ℂ) else 0 := by
  classical
  by_cases hy : y ∈ Set.range f
  · rcases hy with ⟨z, rfl⟩
    rw [Finsupp.mapDomain_apply hf, Finsupp.comapDomain_apply]
    have he : (∃ x, f x = f z ∧ g x = w) ↔ g z = w := by
      constructor
      · rintro ⟨x, hx, hw⟩
        simpa [hf hx] using hw
      · intro h
        exact ⟨z, rfl, h⟩
    rw [he]
    simp [Finsupp.single_apply, eq_comm]
  · rw [Finsupp.mapDomain_notin_range _ _ hy]
    have he : ¬∃ z, f z = y ∧ g z = w := by
      rintro ⟨z, hz, _⟩
      exact hy ⟨z, hz⟩
    simp [he]

theorem prefix_kernel (v u w y : Word α) :
    pureCreate v (erase u (Finsupp.single w 1)) y =
      if ∃ z, v ++ z = y ∧ u ++ z = w then (1 : ℂ) else 0 := by
  classical
  rw [pureCreate_eq_lmapDomain, erase_eq_lcomapDomain]
  exact map_comap_single_kernel _ _ (prefix_injective v) (prefix_injective u) w y

theorem prod_indicator {ι : Type*} [Fintype ι] (p : ι → Prop) :
    (∏ i, if p i then (1 : ℂ) else 0) = if ∀ i, p i then 1 else 0 := by
  classical
  by_cases hp : ∀ i, p i
  · simp [hp]
  · obtain ⟨i, hi⟩ := not_forall.mp hp
    rw [if_neg hp]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Tensor products of delta kernels are delta kernels on the function type. -/
theorem single_function_apply {ι α : Type*} [Fintype ι] (w y : ι → α) :
    (Finsupp.single w (1 : ℂ)) y = ∏ i, (Finsupp.single (w i) (1 : ℂ)) (y i) := by
  classical
  simp only [Finsupp.single_apply]
  rw [prod_indicator]
  congr 1
  exact propext funext_iff

/-- Existential suffixes separate independently over tensor coordinates. -/
theorem tensor_suffix_exists {ι α ζ : Type*}
    (v u : ι → Word α) (w y : (ι → Word α) × ζ) :
    (∃ z : (ι → Word α) × ζ,
      (fun i => v i ++ z.1 i, z.2) = y ∧
      (fun i => u i ++ z.1 i, z.2) = w) ↔
      w.2 = y.2 ∧ ∀ i, ∃ z : Word α, v i ++ z = y.1 i ∧ u i ++ z = w.1 i := by
  constructor
  · rintro ⟨z, hv, hu⟩
    have hv2 := congrArg (fun a : (ι → Word α) × ζ => a.2) hv
    have hu2 := congrArg (fun a : (ι → Word α) × ζ => a.2) hu
    refine ⟨hu2.symm.trans hv2, ?_⟩
    intro i
    exact ⟨z.1 i, congrArg (fun a => a.1 i) hv, congrArg (fun a => a.1 i) hu⟩
  · rintro ⟨hpassive, hs⟩
    choose z hzv hzu using hs
    refine ⟨(z, w.2), ?_, ?_⟩
    · exact Prod.ext (funext hzv) hpassive
    · exact Prod.ext (funext hzu) rfl

/-- The kernel of an amplified tuple prefix operator factors coordinatewise. -/
theorem tensor_prefix_kernel {ι α ζ : Type*} [Fintype ι]
    (v u : ι → Word α) (w y : TensorState α ι ζ) :
    tensorPureCreate v (tensorErase u (Finsupp.single w 1)) y =
      (if w.2 = y.2 then (1 : ℂ) else 0) *
        ∏ t, pureCreate (v t) (erase (u t) (Finsupp.single (w.1 t) 1)) (y.1 t) := by
  classical
  change Finsupp.mapDomain (tensorAppend v)
    (Finsupp.comapDomain (tensorAppend u) (Finsupp.single w (1 : ℂ))
      (tensorAppend_injective u).injOn) y = _
  rw [map_comap_single_kernel _ _ (tensorAppend_injective v) (tensorAppend_injective u)]
  simp only [tensorAppend]
  simp only [tensor_suffix_exists]
  simp_rw [prefix_kernel]
  rw [prod_indicator]
  by_cases hp : w.2 = y.2 <;>
    by_cases ha : ∀ i, ∃ z : Word α, v i ++ z = y.1 i ∧ u i ++ z = w.1 i <;>
    simp [hp, ha]

theorem single_state_apply {ι α ζ : Type*} [Fintype ι]
    (w y : (ι → α) × ζ) :
    (Finsupp.single w (1 : ℂ)) y =
      (if w.2 = y.2 then (1 : ℂ) else 0) *
        ∏ i, (Finsupp.single (w.1 i) (1 : ℂ)) (y.1 i) := by
  classical
  rw [← single_function_apply]
  simp only [Finsupp.single_apply]
  by_cases hf : w.1 = y.1 <;> by_cases hs : w.2 = y.2 <;>
    simp [Prod.ext_iff, hf, hs]

end
end ExplicitFilter


/-! Source component: OneCoordinate.lean -/

open scoped BigOperators
open AdderTrace.PrefixOperators

namespace ExplicitFilter
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

@[simp] theorem erase_nil (f : Word α →₀ ℂ) : erase [] f = f := by
  ext w
  simp

@[simp] theorem pureCreate_nil (f : Word α →₀ ℂ) : pureCreate [] f = f := by
  rw [pureCreate_eq_lmapDomain]
  change Finsupp.mapDomain id f = f
  exact Finsupp.mapDomain_id

def pairPrefix (p : α × α) : Word α := [(p.1, false), (p.2, true)]
def negPrefix (i : α) : Word α := [(i, false)]
def emptyPrefix (_ : Unit) : Word α := []
def reversePairPrefix (p : α × α) : Word α := [(p.2, false), (p.1, true)]

theorem pairPrefix_injective : Function.Injective (pairPrefix (α := α)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simpa [pairPrefix] using h

theorem negPrefix_injective : Function.Injective (negPrefix (α := α)) := by
  intro i j h
  simpa [negPrefix] using h

theorem emptyPrefix_injective : Function.Injective (emptyPrefix (α := α)) := by
  intro i j _
  exact Subsingleton.elim _ _

theorem reversePairPrefix_injective : Function.Injective (reversePairPrefix (α := α)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simpa [reversePairPrefix, and_comm] using h

def zeroCancellation (a : α → α → ℂ) (f : Word α →₀ ℂ) : Word α →₀ ℂ :=
  ∑ i, ∑ j, a i j • pureCreate [(i, false), (j, true)] f

def oneCancellation (a : α → α → ℂ) (f : Word α →₀ ℂ) : Word α →₀ ℂ :=
  ∑ i, ∑ j, a i j • pureCreate [(i, false)] (erase [(j, false)] f)

def twoCancellations (a : α → α → ℂ) (f : Word α →₀ ℂ) : Word α →₀ ℂ :=
  ∑ i, ∑ j, a i j • erase [(j, false), (i, true)] f

/-- The zero-cancellation operator has norm at most the coefficient Frobenius norm. -/
theorem zeroCancellation_bound (a : α → α → ℂ) (f : Word α →₀ ℂ) :
    l2Sq (zeroCancellation a f) ≤ (∑ i, ∑ j, ‖a i j‖ ^ 2) * l2Sq f := by
  have h := l2Sq_prefix_sum_le pairPrefix pairPrefix_injective
    (by intros; simp [pairPrefix]) emptyPrefix emptyPrefix_injective
    (by intros; rfl) (fun p _ => a p.1 p.2) f
  simpa [Fintype.sum_prod_type, pairPrefix, emptyPrefix, zeroCancellation] using h

/-- The one-cancellation operator has the same bound. -/
theorem oneCancellation_bound (a : α → α → ℂ) (f : Word α →₀ ℂ) :
    l2Sq (oneCancellation a f) ≤ (∑ i, ∑ j, ‖a i j‖ ^ 2) * l2Sq f := by
  have h := l2Sq_prefix_sum_le negPrefix negPrefix_injective
    (by intros; simp [negPrefix]) negPrefix negPrefix_injective
    (by intros; simp [negPrefix]) a f
  exact h

/-- The two-cancellation operator has the same bound. -/
theorem twoCancellations_bound (a : α → α → ℂ) (f : Word α →₀ ℂ) :
    l2Sq (twoCancellations a f) ≤ (∑ i, ∑ j, ‖a i j‖ ^ 2) * l2Sq f := by
  have h := l2Sq_prefix_sum_le emptyPrefix emptyPrefix_injective
    (by intros; rfl) reversePairPrefix reversePairPrefix_injective
    (by intros; simp [reversePairPrefix]) (fun _ p => a p.1 p.2) f
  simpa [Fintype.sum_prod_type, reversePairPrefix, emptyPrefix, twoCancellations] using h

/-- The actual left action of the degree-two free-group polynomial,
expressed in its reduced-word basis. -/
def pairConvolution (a : α → α → ℂ) (f : Word α →₀ ℂ) : Word α →₀ ℂ :=
  ∑ i, ∑ j, a i j • pairActionMap i j f

/-- The reduced-word convolution is the compression of its three cancellation pieces. -/
theorem pairConvolution_eq (a : α → α → ℂ) (ha : ∀ i, a i i = 0)
    (f : Word α →₀ ℂ) (hf : reducedProjection f = f) :
    pairConvolution a f = reducedProjection
      (zeroCancellation a f + oneCancellation a f + twoCancellations a f) := by
  have hp (i j : α) : a i j • pairActionMap i j f = reducedProjection
      (a i j • (pureCreate [(i, false), (j, true)] f +
        pureCreate [(i, false)] (erase [(j, false)] f) +
        erase [(j, false), (i, true)] f)) := by
    by_cases hij : i = j
    · subst j
      simp [ha]
    · have h := LinearMap.congr_fun (three_piece_linearMap i j hij) f
      simp only [LinearMap.comp_apply, hf, LinearMap.add_apply] at h
      rw [h, map_smul]
  simp only [pairConvolution, hp, zeroCancellation, oneCancellation, twoCancellations,
    map_add, map_sum, smul_add, Finset.sum_add_distrib]

/-- Elementary one-coordinate Haagerup estimate with the explicit constant three.
This theorem concerns the genuine free-group convolution, not an assumed norm bound. -/
theorem one_coordinate_convolution_bound (a : α → α → ℂ) (ha : ∀ i, a i i = 0)
    (f : Word α →₀ ℂ) (hf : reducedProjection f = f) :
    l2Sq (pairConvolution a f) ≤ 9 * (∑ i, ∑ j, ‖a i j‖ ^ 2) * l2Sq f := by
  rw [pairConvolution_eq a ha f hf]
  have h₀ := zeroCancellation_bound a f
  have h₁ := oneCancellation_bound a f
  have h₂ := twoCancellations_bound a f
  have hp := l2Sq_reducedProjection_le
    (zeroCancellation a f + oneCancellation a f + twoCancellations a f)
  have hs := l2Sq_add_three_le (zeroCancellation a f) (oneCancellation a f)
    (twoCancellations a f)
  nlinarith

end
end ExplicitFilter


/-! Source component: TensorPatternIndices.lean -/

open scoped BigOperators
open AdderTrace.PrefixOperators

namespace ExplicitFilter.TensorPattern
noncomputable section

universe u v
variable {α : Type u} {ι : Type v}

def LeftSlot (α : Type u) (p : Fin 3) : Type _ :=
  if p = 0 then α × α else if p = 1 then α else PUnit.{u+1}

def RightSlot (α : Type u) (p : Fin 3) : Type _ :=
  if p = 0 then PUnit.{u+1} else if p = 1 then α else α × α

instance [Fintype α] (p : Fin 3) : Fintype (LeftSlot α p) := by
  unfold LeftSlot
  split_ifs <;> infer_instance

instance [Fintype α] (p : Fin 3) : Fintype (RightSlot α p) := by
  unfold RightSlot
  split_ifs <;> infer_instance

instance [DecidableEq α] (p : Fin 3) : DecidableEq (LeftSlot α p) := by
  unfold LeftSlot
  split_ifs <;> infer_instance

instance [DecidableEq α] (p : Fin 3) : DecidableEq (RightSlot α p) := by
  unfold RightSlot
  split_ifs <;> infer_instance

def slotEquiv (p : Fin 3) : LeftSlot α p × RightSlot α p ≃ α × α := by
  by_cases h₀ : p = 0
  · simpa [LeftSlot, RightSlot, h₀] using (Equiv.prodPUnit (α × α))
  · by_cases h₁ : p = 1
    · simpa [LeftSlot, RightSlot, h₀, h₁] using (Equiv.refl (α × α))
    · simpa [LeftSlot, RightSlot, h₀, h₁] using (Equiv.punitProd (α × α))

def LeftIndex (p : ι → Fin 3) := ∀ t, LeftSlot α (p t)
def RightIndex (p : ι → Fin 3) := ∀ t, RightSlot α (p t)

instance [Fintype α] [Fintype ι] (p : ι → Fin 3) : Fintype (LeftIndex (α := α) p) := by
  classical
  exact Pi.instFintype
instance [Fintype α] [Fintype ι] (p : ι → Fin 3) : Fintype (RightIndex (α := α) p) := by
  classical
  exact Pi.instFintype
instance [DecidableEq α] [Fintype ι] (p : ι → Fin 3) : DecidableEq (LeftIndex (α := α) p) :=
  Classical.decEq _
instance [DecidableEq α] [Fintype ι] (p : ι → Fin 3) : DecidableEq (RightIndex (α := α) p) :=
  Classical.decEq _

def tensorEquiv (p : ι → Fin 3) :
    LeftIndex (α := α) p × RightIndex (α := α) p ≃ (ι → α) × (ι → α) where
  toFun lr := (fun t => (slotEquiv (p t) (lr.1 t, lr.2 t)).1,
    fun t => (slotEquiv (p t) (lr.1 t, lr.2 t)).2)
  invFun ij := (fun t => ((slotEquiv (p t)).symm (ij.1 t, ij.2 t)).1,
    fun t => ((slotEquiv (p t)).symm (ij.1 t, ij.2 t)).2)
  left_inv lr := by
    apply Prod.ext <;> funext t <;> simp
  right_inv ij := by
    apply Prod.ext <;> funext t <;> simp


def leftSlotPrefix (p : Fin 3) : LeftSlot α p → Word α := by
  by_cases h₀ : p = 0
  · simpa [LeftSlot, h₀] using (pairPrefix (α := α))
  · by_cases h₁ : p = 1
    · simpa [LeftSlot, h₀, h₁] using (negPrefix (α := α))
    · simpa [LeftSlot, h₀, h₁] using (fun _ : PUnit.{u+1} => ([] : Word α))

def rightSlotPrefix (p : Fin 3) : RightSlot α p → Word α := by
  by_cases h₀ : p = 0
  · simpa [RightSlot, h₀] using (fun _ : PUnit.{u+1} => ([] : Word α))
  · by_cases h₁ : p = 1
    · simpa [RightSlot, h₀, h₁] using (negPrefix (α := α))
    · simpa [RightSlot, h₀, h₁] using (reversePairPrefix (α := α))

theorem leftSlotPrefix_injective [Fintype α] [DecidableEq α] (p : Fin 3) :
    Function.Injective (leftSlotPrefix (α := α) p) := by
  fin_cases p
  · simpa [leftSlotPrefix, LeftSlot] using (pairPrefix_injective (α := α))
  · simpa [leftSlotPrefix, LeftSlot] using (negPrefix_injective (α := α))
  · intro x y h
    exact @Subsingleton.elim PUnit _ x y

theorem rightSlotPrefix_injective [Fintype α] [DecidableEq α] (p : Fin 3) :
    Function.Injective (rightSlotPrefix (α := α) p) := by
  fin_cases p
  · intro x y h
    exact @Subsingleton.elim PUnit _ x y
  · simpa [rightSlotPrefix, RightSlot] using (negPrefix_injective (α := α))
  · simpa [rightSlotPrefix, RightSlot] using (reversePairPrefix_injective (α := α))

theorem leftSlotPrefix_length (p : Fin 3) (x : LeftSlot α p) :
    (leftSlotPrefix p x).length = 2 - p.val := by
  fin_cases p <;> simp [leftSlotPrefix, LeftSlot, pairPrefix, negPrefix]

theorem rightSlotPrefix_length (p : Fin 3) (x : RightSlot α p) :
    (rightSlotPrefix p x).length = p.val := by
  fin_cases p <;> simp [rightSlotPrefix, RightSlot, reversePairPrefix, negPrefix]

def leftPrefix (p : ι → Fin 3) (x : LeftIndex (α := α) p) : ι → Word α :=
  fun t => leftSlotPrefix (p t) (x t)

def rightPrefix (p : ι → Fin 3) (x : RightIndex (α := α) p) : ι → Word α :=
  fun t => rightSlotPrefix (p t) (x t)

theorem leftPrefix_injective [Fintype α] [DecidableEq α] (p : ι → Fin 3) :
    Function.Injective (leftPrefix (α := α) p) := by
  intro x y h
  funext t
  exact leftSlotPrefix_injective (p t) (congrFun h t)

theorem rightPrefix_injective [Fintype α] [DecidableEq α] (p : ι → Fin 3) :
    Function.Injective (rightPrefix (α := α) p) := by
  intro x y h
  funext t
  exact rightSlotPrefix_injective (p t) (congrFun h t)

@[simp] theorem leftPrefix_length (p : ι → Fin 3) (x : LeftIndex (α := α) p) (t : ι) :
    (leftPrefix p x t).length = 2 - (p t).val := leftSlotPrefix_length _ _

@[simp] theorem rightPrefix_length (p : ι → Fin 3) (x : RightIndex (α := α) p) (t : ι) :
    (rightPrefix p x t).length = (p t).val := rightSlotPrefix_length _ _


def leftOfPair (c : Fin 3) (i j : α) : Word α :=
  if c = 0 then [(i, false), (j, true)] else if c = 1 then [(i, false)] else []

def rightOfPair (c : Fin 3) (i j : α) : Word α :=
  if c = 0 then [] else if c = 1 then [(j, false)] else [(j, false), (i, true)]

theorem leftSlotPrefix_slotEquiv_symm (c : Fin 3) (i j : α) :
    leftSlotPrefix c ((slotEquiv c).symm (i, j)).1 = leftOfPair c i j := by
  fin_cases c <;> simp [leftSlotPrefix, slotEquiv, leftOfPair, LeftSlot, RightSlot,
    pairPrefix, negPrefix]

theorem rightSlotPrefix_slotEquiv_symm (c : Fin 3) (i j : α) :
    rightSlotPrefix c ((slotEquiv c).symm (i, j)).2 = rightOfPair c i j := by
  fin_cases c <;> simp [rightSlotPrefix, slotEquiv, rightOfPair, LeftSlot, RightSlot,
    reversePairPrefix, negPrefix]

@[simp] theorem leftPrefix_tensorEquiv_symm (p : ι → Fin 3) (i j : ι → α) (t : ι) :
    leftPrefix p ((tensorEquiv p).symm (i, j)).1 t = leftOfPair (p t) (i t) (j t) :=
  leftSlotPrefix_slotEquiv_symm _ _ _

@[simp] theorem rightPrefix_tensorEquiv_symm (p : ι → Fin 3) (i j : ι → α) (t : ι) :
    rightPrefix p ((tensorEquiv p).symm (i, j)).2 t = rightOfPair (p t) (i t) (j t) :=
  rightSlotPrefix_slotEquiv_symm _ _ _


/-- Any sum over prefix row and column indices is the corresponding sum over generator pairs. -/
theorem sum_reindex {E : Type*} [AddCommMonoid E]
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (p : ι → Fin 3) (f : LeftIndex (α := α) p → RightIndex (α := α) p → E) :
    (∑ l, ∑ r, f l r) =
      ∑ i : ι → α, ∑ j : ι → α,
        f ((tensorEquiv p).symm (i, j)).1 ((tensorEquiv p).symm (i, j)).2 := by
  classical
  symm
  simpa only [Fintype.sum_prod_type] using
    (Equiv.sum_comp (tensorEquiv (α := α) p).symm (fun lr => f lr.1 lr.2))

/-- Reindexing coefficients by cancellation prefixes preserves their squared Frobenius norm. -/
theorem frobenius_reindex [Fintype α] [Fintype ι] [DecidableEq ι]
    (p : ι → Fin 3) (a : (ι → α) → (ι → α) → ℂ) :
    (∑ l : LeftIndex (α := α) p, ∑ r : RightIndex (α := α) p,
      ‖a (tensorEquiv p (l, r)).1 (tensorEquiv p (l, r)).2‖ ^ 2) =
    ∑ i, ∑ j, ‖a i j‖ ^ 2 := by
  classical
  simpa only [Fintype.sum_prod_type] using
    (Equiv.sum_comp (tensorEquiv (α := α) p) (fun ij => ‖a ij.1 ij.2‖ ^ 2))

end
end ExplicitFilter.TensorPattern


/-! Source component: ThreePatternKernel.lean -/

open scoped BigOperators Classical
open AdderTrace.PrefixOperators

namespace ExplicitFilter.TensorPattern
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Pointwise three-pattern identity for the actual free-group action on a
reduced input word. The projection condition is attached only to the output. -/
theorem three_pattern_kernel (i j : α) (hij : i ≠ j) (w y : Word α)
    (hw : FreeGroup.IsReduced w) :
    (Finsupp.single (FreeGroup.reduce ((i, false) :: (j, true) :: w)) (1 : ℂ)) y =
      if FreeGroup.IsReduced y then
        ∑ c : Fin 3,
          (pureCreate (leftOfPair c i j)
            (erase (rightOfPair c i j) (Finsupp.single w 1))) y
      else 0 := by
  have h := congrArg (fun f : Word α →₀ ℂ => f y)
    (three_piece_compression i j hij w hw)
  rw [reducedProjection_eq_filter] at h
  by_cases hy : FreeGroup.IsReduced y <;>
    simpa [hy, Finsupp.filter_apply, Fin.sum_univ_three, leftOfPair, rightOfPair] using h

/-- On a reduced output word the three kernels sum directly. -/
theorem three_pattern_kernel_of_reduced (i j : α) (hij : i ≠ j) (w y : Word α)
    (hw : FreeGroup.IsReduced w) (hy : FreeGroup.IsReduced y) :
    (Finsupp.single (FreeGroup.reduce ((i, false) :: (j, true) :: w)) (1 : ℂ)) y =
      ∑ c : Fin 3,
        (pureCreate (leftOfPair c i j)
          (erase (rightOfPair c i j) (Finsupp.single w 1))) y := by
  simpa [hy] using three_pattern_kernel i j hij w y hw

end
end ExplicitFilter.TensorPattern


/-! Source component: TensorPatternBounds.lean -/

open scoped BigOperators
open AdderTrace.PrefixOperators

namespace ExplicitFilter.TensorPattern
noncomputable section

variable {α ι ζ : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-- One prescribed cancellation pattern, amplified by an arbitrary passive space. -/
def cancellationPiece (p : ι → Fin 3) (a : (ι → α) → (ι → α) → ℂ)
    (f : TensorState α ι ζ →₀ ℂ) : TensorState α ι ζ →₀ ℂ :=
  ∑ l : LeftIndex (α := α) p, ∑ r : RightIndex (α := α) p,
    a (tensorEquiv p (l, r)).1 (tensorEquiv p (l, r)).2 •
      tensorPureCreate (leftPrefix p l) (tensorErase (rightPrefix p r) f)

/-- Prefix orthogonality bounds every tensor cancellation pattern by the same
coefficient Frobenius norm, independently of the number of coordinates. -/
theorem cancellationPiece_bound (p : ι → Fin 3) (a : (ι → α) → (ι → α) → ℂ)
    (f : TensorState α ι ζ →₀ ℂ) :
    l2Sq (cancellationPiece p a f) ≤ (∑ i, ∑ j, ‖a i j‖ ^ 2) * l2Sq f := by
  have h := l2Sq_tensor_prefix_sum_le
    (leftPrefix (α := α) p) (leftPrefix_injective p) (by intros; simp)
    (rightPrefix (α := α) p) (rightPrefix_injective p) (by intros; simp)
    (fun l r => a (tensorEquiv p (l, r)).1 (tensorEquiv p (l, r)).2) f
  rw [frobenius_reindex] at h
  exact h

/-- Direct generator-pair expression for a cancellation pattern. -/
theorem cancellationPiece_eq (p : ι → Fin 3) (a : (ι → α) → (ι → α) → ℂ)
    (f : TensorState α ι ζ →₀ ℂ) :
    cancellationPiece p a f =
      ∑ i, ∑ j, a i j •
        tensorPureCreate (fun t => leftOfPair (p t) (i t) (j t))
          (tensorErase (fun t => rightOfPair (p t) (i t) (j t)) f) := by
  unfold cancellationPiece
  rw [sum_reindex]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : tensorEquiv p
      (((tensorEquiv p).symm (i, j)).1, ((tensorEquiv p).symm (i, j)).2) = (i, j) :=
    (tensorEquiv p).apply_symm_apply (i, j)
  rw [hij]
  have hl : leftPrefix p ((tensorEquiv p).symm (i, j)).1 =
      fun t => leftOfPair (p t) (i t) (j t) := by funext t; simp
  have hr : rightPrefix p ((tensorEquiv p).symm (i, j)).2 =
      fun t => rightOfPair (p t) (i t) (j t) := by funext t; simp
  rw [hl, hr]

/-- Summing the `3^r` cancellation patterns costs `9^r` in squared norm. -/
theorem cancellation_sum_bound (a : (ι → α) → (ι → α) → ℂ)
    (f : TensorState α ι ζ →₀ ℂ) :
    l2Sq (∑ p : ι → Fin 3, cancellationPiece p a f) ≤
      (9 : ℝ) ^ Fintype.card ι * (∑ i, ∑ j, ‖a i j‖ ^ 2) * l2Sq f := by
  classical
  have hc : (Fintype.card (ι → Fin 3) : ℝ) = (3 : ℝ) ^ Fintype.card ι := by
    simp
  calc
    _ ≤ (Fintype.card (ι → Fin 3) : ℝ) *
        ∑ p : ι → Fin 3, l2Sq (cancellationPiece p a f) := by
      simpa using l2Sq_sum_le (Finset.univ : Finset (ι → Fin 3))
        (fun p => cancellationPiece p a f)
    _ ≤ (Fintype.card (ι → Fin 3) : ℝ) *
        ∑ _p : ι → Fin 3, (∑ i, ∑ j, ‖a i j‖ ^ 2) * l2Sq f := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun p _ => cancellationPiece_bound p a f)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
      calc
        _ = ((3 : ℝ) ^ Fintype.card ι * 3 ^ Fintype.card ι) *
            (∑ i, ∑ j, ‖a i j‖ ^ 2) * l2Sq f := by ring
        _ = _ := by rw [← mul_pow]; norm_num

/-- The same bound after projection onto reduced words. -/
theorem projected_cancellation_sum_bound (a : (ι → α) → (ι → α) → ℂ)
    (f : TensorState α ι ζ →₀ ℂ) :
    l2Sq (tensorProjection (∑ p : ι → Fin 3, cancellationPiece p a f)) ≤
      (9 : ℝ) ^ Fintype.card ι * (∑ i, ∑ j, ‖a i j‖ ^ 2) * l2Sq f :=
  (l2Sq_tensorProjection_le _).trans (cancellation_sum_bound a f)

end
end ExplicitFilter.TensorPattern


/-! Source component: TensorCancellation.lean -/

open scoped BigOperators Classical
open AdderTrace.PrefixOperators
open ExplicitFilter.TensorPattern

namespace ExplicitFilter
noncomputable section
set_option maxHeartbeats 50000
attribute [local irreducible] pureCreate erase leftOfPair rightOfPair

variable {ι α ζ : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem pattern_prod_sum (K : ι → Fin 3 → ℂ) :
    (∏ t, ∑ c : Fin 3, K t c) = ∑ p : ι → Fin 3, ∏ t, K t (p t) := by
  exact Fintype.prod_sum K

/-- The product of the three one-coordinate cancellation decompositions is
the exact `3^r`-pattern decomposition on each reduced tuple basis vector. -/
theorem tupleAction_single_eq_patterns (I J : ι → α) (hIJ : ∀ t, I t ≠ J t)
    (w : TensorState α ι ζ) (hw : ∀ t, FreeGroup.IsReduced (w.1 t)) :
    tupleActionMapWithSuffix I J (Finsupp.single w 1) =
      tensorProjection (∑ p : ι → Fin 3,
        tensorPureCreate (fun t => leftOfPair (p t) (I t) (J t))
          (tensorErase (fun t => rightOfPair (p t) (I t) (J t))
            (Finsupp.single w 1))) := by
  classical
  ext y
  simp only [tupleActionMapWithSuffix, Finsupp.linearCombination_single, one_smul,
    tensorProjection_apply]
  by_cases hy : ∀ t, FreeGroup.IsReduced (y.1 t)
  · rw [if_pos hy, single_state_apply]
    simp only [Finsupp.finset_sum_apply, tensor_prefix_kernel]
    rw [← Finset.mul_sum]
    apply congrArg (fun z : ℂ => (if w.2 = y.2 then (1 : ℂ) else 0) * z)
    simp only [tupleWordAction]
    calc
      (∏ t, (Finsupp.single
        (FreeGroup.reduce ((I t, false) :: (J t, true) :: w.1 t)) (1 : ℂ)) (y.1 t)) =
          ∏ t, ∑ c : Fin 3,
            pureCreate (leftOfPair c (I t) (J t))
              (erase (rightOfPair c (I t) (J t)) (Finsupp.single (w.1 t) 1)) (y.1 t) := by
        apply Finset.prod_congr rfl
        intro t ht
        exact three_pattern_kernel_of_reduced _ _ (hIJ t) _ _ (hw t) (hy t)
      _ = ∑ p : ι → Fin 3, ∏ t,
          pureCreate (leftOfPair (p t) (I t) (J t))
            (erase (rightOfPair (p t) (I t) (J t)) (Finsupp.single (w.1 t) 1)) (y.1 t) :=
        pattern_prod_sum _
      _ = _ := by
        apply Finset.sum_congr (by ext; simp)
        intro p hp
        apply Finset.prod_congr (by ext; simp)
        intro t ht
        exact congrArg (fun d : DecidableEq α =>
          pureCreate (leftOfPair (p t) (I t) (J t))
            ((@erase α d (rightOfPair (p t) (I t) (J t)))
              (Finsupp.single (w.1 t) 1)) (y.1 t)) (Subsingleton.elim _ _)
  · rw [if_neg hy]
    apply Finsupp.single_eq_of_ne
    intro heq
    apply hy
    intro t
    have ht := congrArg (fun z : TensorState α ι ζ => z.1 t) heq
    change y.1 t = tupleWordAction I J w.1 t at ht
    rw [ht]
    exact FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce.idem)

end
end ExplicitFilter


/-! Source component: HomogeneousTensor.lean -/

open scoped BigOperators Classical
open AdderTrace.PrefixOperators
open ExplicitFilter.TensorPattern

namespace ExplicitFilter
noncomputable section
attribute [local irreducible] pureCreate erase leftOfPair rightOfPair
  tensorPureCreate tensorErase

variable {ι α ζ : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- A fixed pair of generator tuples, restricted to reduced input tuples,
is exactly the compression of its cancellation-pattern sum. -/
theorem tupleAction_eq_patterns (I J : ι → α) (hIJ : ∀ t, I t ≠ J t)
    (f : TensorState α ι ζ →₀ ℂ) (hf : tensorProjection f = f) :
    tupleActionMapWithSuffix I J f =
      tensorProjection (∑ p : ι → Fin 3,
        tensorPureCreate (fun t => leftOfPair (p t) (I t) (J t))
          (tensorErase (fun t => rightOfPair (p t) (I t) (J t)) f)) := by
  classical
  let P : (TensorState α ι ζ →₀ ℂ) →ₗ[ℂ] (TensorState α ι ζ →₀ ℂ) :=
    ∑ p : ι → Fin 3,
      (tensorPureCreate (fun t => leftOfPair (p t) (I t) (J t))).comp
        (tensorErase (fun t => rightOfPair (p t) (I t) (J t)))
  have hmaps : (tupleActionMapWithSuffix (ζ := ζ) I J).comp tensorProjection =
      tensorProjection.comp (P.comp tensorProjection) := by
    apply Finsupp.lhom_ext
    intro w c
    have hs : Finsupp.single w c = c • Finsupp.single w (1 : ℂ) := by simp
    rw [hs]
    simp only [map_smul]
    apply congrArg (fun v => c • v)
    by_cases hw : ∀ t, FreeGroup.IsReduced (w.1 t)
    · have hQ : tensorProjection (Finsupp.single w (1 : ℂ)) = Finsupp.single w 1 :=
        tensorProjection_single w 1 hw
      simp only [LinearMap.comp_apply, hQ, P, LinearMap.sum_apply]
      simpa only [LinearMap.comp_apply] using tupleAction_single_eq_patterns I J hIJ w hw
    · have hQ : tensorProjection (Finsupp.single w (1 : ℂ)) = 0 := by
        ext y
        rw [tensorProjection_apply, Finsupp.zero_apply]
        split_ifs with hy
        · apply Finsupp.single_eq_of_ne
          intro heq
          exact hw (by simpa [heq] using hy)
        · rfl
      simp only [LinearMap.comp_apply, hQ, map_zero]
  have h := LinearMap.congr_fun hmaps f
  simpa only [LinearMap.comp_apply, hf, P, LinearMap.sum_apply] using h

/-- The actual homogeneous tensor free polynomial equals the sum of its
`3^r` cancellation patterns, compressed to reduced tuples. -/
theorem homogeneous_tensor_convolution_eq (a : (ι → α) → (ι → α) → ℂ)
    (ha : ∀ I J, (∃ t, I t = J t) → a I J = 0)
    (f : TensorState α ι ζ →₀ ℂ) (hf : tensorProjection f = f) :
    tupleConvolutionWithSuffix a f =
      tensorProjection (∑ p : ι → Fin 3, cancellationPiece p a f) := by
  classical
  have hterm (I J : ι → α) :
      a I J • tupleActionMapWithSuffix I J f =
        a I J • tensorProjection (∑ p : ι → Fin 3,
          tensorPureCreate (fun t => leftOfPair (p t) (I t) (J t))
            (tensorErase (fun t => rightOfPair (p t) (I t) (J t)) f)) := by
    by_cases hIJ : ∀ t, I t ≠ J t
    · rw [tupleAction_eq_patterns I J hIJ f hf]
    · have hz : a I J = 0 := ha I J (by simpa only [not_forall, not_not] using hIJ)
      simp [hz]
  simp only [tupleConvolutionWithSuffix, hterm, cancellationPiece_eq, map_sum,
    map_smul, Finset.smul_sum]
  calc
    (∑ I, ∑ J, ∑ p : ι → Fin 3, a I J • tensorProjection
      (tensorPureCreate (fun t => leftOfPair (p t) (I t) (J t))
        (tensorErase (fun t => rightOfPair (p t) (I t) (J t)) f))) =
      ∑ I, ∑ p : ι → Fin 3, ∑ J, a I J • tensorProjection
        (tensorPureCreate (fun t => leftOfPair (p t) (I t) (J t))
          (tensorErase (fun t => rightOfPair (p t) (I t) (J t)) f)) := by
      apply Finset.sum_congr rfl
      intro I hI
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The homogeneous tensor free-group estimate, with an arbitrary untouched
register. This is a theorem about the actual convolution operators. -/
theorem homogeneous_tensor_convolution_bound (a : (ι → α) → (ι → α) → ℂ)
    (ha : ∀ I J, (∃ t, I t = J t) → a I J = 0)
    (f : TensorState α ι ζ →₀ ℂ) (hf : tensorProjection f = f) :
    l2Sq (tupleConvolutionWithSuffix a f) ≤
      (9 : ℝ) ^ Fintype.card ι * (∑ I, ∑ J, ‖a I J‖ ^ 2) * l2Sq f := by
  rw [homogeneous_tensor_convolution_eq a ha f hf]
  exact projected_cancellation_sum_bound a f

end
end ExplicitFilter


/-! Source component: FullTensorBound.lean -/

open scoped BigOperators

namespace ExplicitFilter
noncomputable section

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α] [Nonempty α]

/-- Every support slice obeys the explicit tensor bound after collapsing its
common inactive generator labels. All action and coefficient identifications
are supplied by the preceding concrete lemmas. -/
theorem support_slice_convolution_bound
    (W : (ι → α) → (ι → α) → ℂ) (S : Finset ι)
    (f : TupleWord ι α →₀ ℂ)
    (hf : ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) :
    l2Sq (tupleConvolution (coefficientSlice W S) f) ≤
      sliceWeight (α := α) S * (∑ I, ∑ J, ‖coefficientSlice W S I J‖ ^ 2) * l2Sq f := by
  apply slice_convolution_bound_of_collapsed W S f hf
  exact homogeneous_tensor_convolution_bound (collapsedSlice W S)
    (collapsedSlice_zero W S) (splitWordMap S f) (tensorProjection_splitWordMap S f hf)

/-- The full, unconditional free tensor polynomial estimate with the exact
constant `(M+9)^r-M^r`. No operator norm or moment bound is assumed. -/
theorem full_tensor_convolution_bound
    (W : (ι → α) → (ι → α) → ℂ) (hW : ∀ I, W I I = 0)
    (f : TupleWord ι α →₀ ℂ)
    (hf : ∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) :
    l2Sq (tupleConvolution W f) ≤
      (((Fintype.card α : ℝ) + 9) ^ Fintype.card ι -
        (Fintype.card α : ℝ) ^ Fintype.card ι) *
          (∑ I, ∑ J, ‖W I J‖ ^ 2) * l2Sq f := by
  apply full_convolution_bound_of_slices W hW f
  intro S _
  exact support_slice_convolution_bound W S f hf

end
end ExplicitFilter


/-! Source component: GroupMoment.lean -/

open scoped BigOperators ComplexConjugate

namespace AdderTrace

variable {G : Type*} [Group G]

/-- The identity coefficient of `a * b` is the squared coefficient norm
when `a` and `b` are convolution adjoints. -/
theorem convolution_identity_coefficient_of_adjoint
    (a b : MonoidAlgebra ℂ G)
    (hadjoint : ∀ g, a (g⁻¹) = conj (b g)) :
    (a * b) 1 = (∑ g ∈ b.support, ‖b g‖ ^ 2 : ℝ) := by
  classical
  rw [MonoidAlgebra.mul_apply_right]
  simp only [one_mul, Finsupp.sum, hadjoint,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    Complex.ofReal_sum]

/-- A symmetric half-power converts the even identity moment exactly to
its squared coefficient norm. -/
theorem even_identity_moment_eq_l2
    (a : MonoidAlgebra ℂ G) (L : ℕ)
    (hhalf : ∀ g, (a ^ L) (g⁻¹) = conj ((a ^ L) g)) :
    (a ^ (2 * L)) 1 = (∑ g ∈ (a ^ L).support, ‖(a ^ L) g‖ ^ 2 : ℝ) := by
  rw [two_mul, pow_add]
  exact convolution_identity_coefficient_of_adjoint _ _ hhalf

omit [Group G] in
/-- Restricting a squared coefficient sum to any finite set can only decrease it. -/
theorem sum_norm_sq_le_support (a : G →₀ ℂ) (s : Finset G) :
    (∑ g ∈ s, ‖a g‖ ^ 2) ≤ ∑ g ∈ a.support, ‖a g‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ g ∈ s ∪ a.support, ‖a g‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun _ _ _ => sq_nonneg _)
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro g hg hnot
      simp [Finsupp.notMem_support_iff.mp hnot]

/-- Cauchy--Schwarz for the identity coefficient of convolution. -/
theorem norm_identity_convolution_le (a b : MonoidAlgebra ℂ G) :
    ‖(a * b) 1‖ ≤
      Real.sqrt (∑ g ∈ a.support, ‖a g‖ ^ 2) *
      Real.sqrt (∑ g ∈ b.support, ‖b g‖ ^ 2) := by
  classical
  have hinv : (∑ g ∈ b.support, ‖a g⁻¹‖ ^ 2) ≤
      ∑ g ∈ a.support, ‖a g‖ ^ 2 := by
    calc
      _ = ∑ g ∈ b.support.image Inv.inv, ‖a g‖ ^ 2 := by
        rw [Finset.sum_image]
        exact fun x hx y hy h => inv_injective h
      _ ≤ _ := sum_norm_sq_le_support a _
  rw [MonoidAlgebra.mul_apply_right]
  simp only [Finsupp.sum, one_mul]
  calc
    _ ≤ ∑ g ∈ b.support, ‖a g⁻¹ * b g‖ := norm_sum_le _ _
    _ = ∑ g ∈ b.support, ‖a g⁻¹‖ * ‖b g‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ g ∈ b.support, ‖a g⁻¹‖ ^ 2) *
        Real.sqrt (∑ g ∈ b.support, ‖b g‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hinv)
      (Real.sqrt_nonneg _)

/-- Every even identity moment is bounded by the squared coefficient norm
of the half-power.  This needs no self-adjointness assumption. -/
theorem norm_even_identity_moment_le (a : MonoidAlgebra ℂ G) (L : ℕ) :
    ‖(a ^ (2 * L)) 1‖ ≤ ∑ g ∈ (a ^ L).support, ‖(a ^ L) g‖ ^ 2 := by
  rw [two_mul, pow_add]
  have h := norm_identity_convolution_le (a ^ L) (a ^ L)
  rwa [Real.mul_self_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at h

end AdderTrace


/-! Source component: MomentIteration.lean -/

/-! Iterating a proved convolution estimate controls all even identity moments. -/

namespace ExplicitFilter

variable {G : Type*} [Group G]

@[simp] theorem l2Sq_monoidAlgebra_one :
    l2Sq (1 : MonoidAlgebra ℂ G) = 1 := by
  classical
  simp [l2Sq, MonoidAlgebra.one_def, MonoidAlgebra.single,
    Finsupp.support_single_ne_zero _ (one_ne_zero : (1 : ℂ) ≠ 0)]

/-- A uniform squared-norm bound for left multiplication iterates to powers. -/
theorem l2Sq_pow_le (a : MonoidAlgebra ℂ G) (D : ℝ) (hD : 0 ≤ D)
    (hoperator : ∀ x : MonoidAlgebra ℂ G, l2Sq (a * x) ≤ D * l2Sq x)
    (L : ℕ) : l2Sq (a ^ L) ≤ D ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [pow_succ']
    calc
      _ ≤ D * l2Sq (a ^ L) := hoperator _
      _ ≤ D * D ^ L := mul_le_mul_of_nonneg_left ih hD
      _ = D ^ (L + 1) := (pow_succ' D L).symm

/-- A uniform convolution bound gives the even identity-moment bound needed
in the trace argument, with no spectral theory or self-adjointness premise. -/
theorem even_group_moment_le (a : MonoidAlgebra ℂ G) (R : ℝ)
    (hoperator : ∀ x : MonoidAlgebra ℂ G,
      l2Sq (a * x) ≤ R ^ 2 * l2Sq x) (L : ℕ) :
    ‖(a ^ (2 * L)) 1‖ ≤ R ^ (2 * L) := by
  calc
    _ ≤ l2Sq (a ^ L) := AdderTrace.norm_even_identity_moment_le a L
    _ ≤ (R ^ 2) ^ L := l2Sq_pow_le a (R ^ 2) (sq_nonneg R) hoperator L
    _ = R ^ (2 * L) := (pow_mul R 2 L).symm

end ExplicitFilter


/-! Source component: GroupWordBridge.lean -/

open scoped BigOperators ComplexConjugate
open AdderTrace.PrefixOperators

namespace ExplicitFilter
noncomputable section

variable {ι α : Type*} [DecidableEq α]

/-- Tensor tuples of canonical free generators. -/
def generatorTuple (I : ι → α) : ι → FreeGroup α := fun t => FreeGroup.of (I t)

/-- Canonical reduced-word coordinates on a direct product of free groups. -/
def tupleWordEmbedding : (ι → FreeGroup α) ↪ TupleWord ι α where
  toFun g t := (g t).toWord
  inj' := by
    intro g h hgh
    funext t
    exact FreeGroup.toWord_injective (congrFun hgh t)

/-- Embedding the actual group algebra into its reduced-word coordinates. -/
def embedGroupWords : MonoidAlgebra ℂ (ι → FreeGroup α) →ₗ[ℂ]
    (TupleWord ι α →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ tupleWordEmbedding

lemma embedGroupWords_eq_embDomain (f : MonoidAlgebra ℂ (ι → FreeGroup α)) :
    embedGroupWords f = Finsupp.embDomain tupleWordEmbedding f := by
  change Finsupp.mapDomain tupleWordEmbedding f = _
  exact (Finsupp.embDomain_eq_mapDomain tupleWordEmbedding f).symm

@[simp] lemma embedGroupWords_single (g : ι → FreeGroup α) (c : ℂ) :
    embedGroupWords (MonoidAlgebra.single g c) =
      Finsupp.single (tupleWordEmbedding g) c := by
  rw [embedGroupWords_eq_embDomain]
  exact Finsupp.embDomain_single _ _ _

@[simp] lemma l2Sq_embedGroupWords (f : MonoidAlgebra ℂ (ι → FreeGroup α)) :
    l2Sq (embedGroupWords f) = l2Sq f := by
  rw [embedGroupWords_eq_embDomain, l2Sq_embDomain]

lemma embedGroupWords_support_reduced (f : MonoidAlgebra ℂ (ι → FreeGroup α))
    (w : TupleWord ι α) (hw : w ∈ (embedGroupWords f).support) :
    ∀ t, FreeGroup.IsReduced (w t) := by
  classical
  rw [embedGroupWords_eq_embDomain, Finsupp.support_embDomain] at hw
  obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hw
  intro t
  exact FreeGroup.isReduced_toWord

/-- The direct-product group action agrees with simultaneous reduced prefixing. -/
lemma tupleWordEmbedding_pair_mul (I J : ι → α) (g : ι → FreeGroup α) :
    tupleWordEmbedding ((generatorTuple I)⁻¹ * generatorTuple J * g) =
      tupleWordAction I J (tupleWordEmbedding g) := by
  funext t
  change (((FreeGroup.of (I t))⁻¹ * FreeGroup.of (J t)) * g t).toWord = _
  rw [mul_assoc, FreeGroup.toWord_mul, FreeGroup.toWord_inv, FreeGroup.toWord_of,
    FreeGroup.toWord_mul, FreeGroup.toWord_of]
  simp only [FreeGroup.invRev, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.map_cons, List.map_nil, Bool.not_true, List.cons_append,
    FreeGroup.reduce_cons_reduce]
  rfl

/-- Multiplication by a group-basis pair intertwines with the tuple action. -/
lemma embedGroupWords_pair_mul (I J : ι → α)
    (f : MonoidAlgebra ℂ (ι → FreeGroup α)) :
    embedGroupWords (MonoidAlgebra.single
      ((generatorTuple I)⁻¹ * generatorTuple J) (1 : ℂ) * f) =
      tupleActionMap I J (embedGroupWords f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [mul_add, map_add, hf, hg]
  | single g c =>
    simp [MonoidAlgebra.single_mul_single, embedGroupWords_single, tupleActionMap,
      tupleWordEmbedding_pair_mul]

variable [Fintype ι] [DecidableEq ι] [Fintype α]

/-- The precise free-group polynomial corresponding to the matrix coefficients. -/
def freePolynomial (W : Matrix (ι → α) (ι → α) ℂ) :
    MonoidAlgebra ℂ (ι → FreeGroup α) :=
  ∑ I, ∑ J, W I J • MonoidAlgebra.single ((generatorTuple I)⁻¹ * generatorTuple J) 1

/-- The concrete group-algebra convolution is exactly the word-tuple convolution. -/
theorem embedGroupWords_polynomial_mul (W : Matrix (ι → α) (ι → α) ℂ)
    (f : MonoidAlgebra ℂ (ι → FreeGroup α)) :
    embedGroupWords (freePolynomial W * f) = tupleConvolution W (embedGroupWords f) := by
  simp only [freePolynomial, Finset.sum_mul, Algebra.smul_mul_assoc,
    map_sum, map_smul, embedGroupWords_pair_mul, tupleConvolution]

lemma freePolynomial_apply (W : Matrix (ι → α) (ι → α) ℂ)
    (g : ι → FreeGroup α) :
    freePolynomial W g = ∑ I, ∑ J,
      W I J * (if (generatorTuple I)⁻¹ * generatorTuple J = g then 1 else 0) := by
  classical
  change ((∑ I, ∑ J, W I J • Finsupp.single
    ((generatorTuple I)⁻¹ * generatorTuple J) (1 : ℂ) :
      (ι → FreeGroup α) →₀ ℂ) g) = _
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply]

/-- Hermitian coefficients give the actual inverse/conjugate symmetry
of the free-group polynomial. -/
theorem freePolynomial_hermitian (W : Matrix (ι → α) (ι → α) ℂ)
    (hW : W.IsHermitian) (g : ι → FreeGroup α) :
    freePolynomial W g⁻¹ = conj (freePolynomial W g) := by
  classical
  rw [freePolynomial_apply, freePolynomial_apply]
  simp only [map_sum, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← hW.apply J I]
  congr 1
  simp only [apply_ite, map_one, map_zero]
  have hiff : (generatorTuple J)⁻¹ * generatorTuple I = g⁻¹ ↔
      (generatorTuple I)⁻¹ * generatorTuple J = g := by
    constructor
    · intro h
      have hi := congrArg Inv.inv h
      simpa only [mul_inv_rev, inv_inv] using hi
    · intro h
      have hi := congrArg Inv.inv h
      simpa only [mul_inv_rev, inv_inv] using hi
  simp [hiff]

/-- Any established tuple-convolution bound transfers to the concrete
free-group polynomial without a representation-theoretic assumption. -/
theorem freePolynomial_convolution_bound
    (W : Matrix (ι → α) (ι → α) ℂ) (D : ℝ)
    (hword : ∀ f : TupleWord ι α →₀ ℂ,
      (∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) →
      l2Sq (tupleConvolution W f) ≤ D * l2Sq f)
    (f : MonoidAlgebra ℂ (ι → FreeGroup α)) :
    l2Sq (freePolynomial W * f) ≤ D * l2Sq f := by
  rw [← l2Sq_embedGroupWords (freePolynomial W * f), embedGroupWords_polynomial_mul,
    ← l2Sq_embedGroupWords f]
  exact hword _ (embedGroupWords_support_reduced f)

/-- Concrete free-polynomial even moments follow from the tuple estimate. -/
theorem freePolynomial_even_moment_bound
    (W : Matrix (ι → α) (ι → α) ℂ) (R : ℝ)
    (hword : ∀ f : TupleWord ι α →₀ ℂ,
      (∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) →
      l2Sq (tupleConvolution W f) ≤ R ^ 2 * l2Sq f) (L : ℕ) :
    ‖(freePolynomial W ^ (2 * L)) 1‖ ≤ R ^ (2 * L) := by
  exact even_group_moment_le (freePolynomial W) R
    (freePolynomial_convolution_bound W (R ^ 2) hword) L

end
end ExplicitFilter


/-! Source component: AdderCones.lean -/

/-!
Elementary ping-pong for the two integer adders.

`upper t` sends (a,b) to (a+2tb,b), and `lower m` sends (a,b)
to (a,b+2ma).  Their conjugates freely generate, in the explicit
sense that every nonempty reduced syllable word acts nontrivially.
All statements below are unconditional and checked by Lean.
-/

namespace AdderCones

abbrev Label := ℤ × ℤ

def upper (t : ℤ) (x : Label) : Label := (x.1 + 2 * t * x.2, x.2)

def lower (m : ℤ) (x : Label) : Label := (x.1, x.2 + 2 * m * x.1)

def step (i : ℕ) (m : ℤ) (x : Label) : Label :=
  let c := x.1 - 2 * (i : ℤ) * x.2
  let b := x.2 + 2 * m * c
  (c + 2 * (i : ℤ) * b, b)

theorem step_eq_conjugate (i : ℕ) (m : ℤ) (x : Label) :
    step i m x = upper (i : ℤ) (lower m (upper (-(i : ℤ)) x)) := by
  apply Prod.ext <;> dsimp [step, upper, lower] <;> ring

theorem upper_add (s t : ℤ) (x : Label) :
    upper s (upper t x) = upper (s + t) x := by
  apply Prod.ext
  · dsimp [upper]
    ring
  · rfl

theorem lower_add (s t : ℤ) (x : Label) :
    lower s (lower t x) = lower (s + t) x := by
  apply Prod.ext
  · rfl
  · dsimp [lower]
    ring

def upperPerm (t : ℤ) : Equiv.Perm Label where
  toFun := upper t
  invFun := upper (-t)
  left_inv x := by rw [upper_add]; simp [upper]
  right_inv x := by rw [upper_add]; simp [upper]

def lowerPerm (m : ℤ) : Equiv.Perm Label where
  toFun := lower m
  invFun := lower (-m)
  left_inv x := by rw [lower_add]; simp [lower]
  right_inv x := by rw [lower_add]; simp [lower]

def upperHom : Multiplicative ℤ →* Equiv.Perm Label where
  toFun t := upperPerm t.toAdd
  map_one' := by
    apply Equiv.ext
    intro x
    simp [upperPerm, upper]
  map_mul' s t := by
    apply Equiv.ext
    intro x
    exact (upper_add s.toAdd t.toAdd x).symm

def lowerHom : Multiplicative ℤ →* Equiv.Perm Label where
  toFun m := lowerPerm m.toAdd
  map_one' := by
    apply Equiv.ext
    intro x
    simp [lowerPerm, lower]
  map_mul' s t := by
    apply Equiv.ext
    intro x
    exact (lower_add s.toAdd t.toAdd x).symm

theorem upperPerm_eq_zpow (t : ℤ) : upperPerm t = (upperPerm 1) ^ t := by
  have h := map_zpow upperHom (Multiplicative.ofAdd (1 : ℤ)) t
  simpa [upperHom, toAdd_zpow] using h

theorem lowerPerm_eq_zpow (m : ℤ) : lowerPerm m = (lowerPerm 1) ^ m := by
  have h := map_zpow lowerHom (Multiplicative.ofAdd (1 : ℤ)) m
  simpa [lowerHom, toAdd_zpow] using h

theorem step_add (i : ℕ) (s t : ℤ) (x : Label) :
    step i s (step i t x) = step i (s + t) x := by
  apply Prod.ext <;> dsimp [step] <;> ring

theorem step_zero (i : ℕ) (x : Label) : step i 0 x = x := by
  apply Prod.ext <;> dsimp [step] <;> ring

theorem step_inverse (i : ℕ) (m : ℤ) (x : Label) :
    step i (-m) (step i m x) = x := by
  rw [step_add]
  simp only [neg_add_cancel]
  exact step_zero i x

def stepPerm (i : ℕ) (m : ℤ) : Equiv.Perm Label where
  toFun := step i m
  invFun := step i (-m)
  left_inv := step_inverse i m
  right_inv x := by
    rw [step_add]
    simp only [add_neg_cancel]
    exact step_zero i x

def stepHom (i : ℕ) : Multiplicative ℤ →* Equiv.Perm Label where
  toFun m := stepPerm i m.toAdd
  map_one' := by
    apply Equiv.ext
    intro x
    exact step_zero i x
  map_mul' s t := by
    apply Equiv.ext
    intro x
    exact (step_add i s.toAdd t.toAdd x).symm

/-- The parameter m is the genuine integer power of the generator. -/
theorem stepPerm_eq_zpow (i : ℕ) (m : ℤ) :
    stepPerm i m = (stepPerm i 1) ^ m := by
  have h := map_zpow (stepHom i) (Multiplicative.ofAdd (1 : ℤ)) m
  simpa [stepHom, toAdd_zpow] using h

/-- Exact identification with the two adder permutations and their integer powers. -/
theorem stepPerm_eq_adder_conjugate (i : ℕ) (m : ℤ) :
    stepPerm i m =
      (upperPerm 1) ^ (i : ℤ) * (lowerPerm 1) ^ m *
        (upperPerm 1) ^ (-(i : ℤ)) := by
  rw [← upperPerm_eq_zpow, ← lowerPerm_eq_zpow, ← upperPerm_eq_zpow]
  apply Equiv.ext
  intro x
  exact step_eq_conjugate i m x

def InCone (i : ℕ) (x : Label) : Prop :=
  |x.1 - 2 * (i : ℤ) * x.2| < |x.2|

theorem other_cone (i j : ℕ) (hij : i ≠ j) (x : Label)
    (hx : InCone i x) :
    |x.2| < |x.1 - 2 * (j : ℤ) * x.2| := by
  have hdiff : (i : ℤ) - (j : ℤ) ≠ 0 := by omega
  have habs : 1 ≤ |(i : ℤ) - (j : ℤ)| := by
    have := abs_pos.mpr hdiff
    omega
  have hlarge :
      2 * |x.2| ≤ |2 * ((i : ℤ) - (j : ℤ)) * x.2| := by
    rw [abs_mul, abs_mul]
    norm_num
    have hp := mul_le_mul_of_nonneg_right habs (abs_nonneg x.2)
    have htwice := mul_le_mul_of_nonneg_left hp (show (0 : ℤ) ≤ 2 by omega)
    simpa only [mul_one, one_mul, mul_assoc] using htwice
  have hid :
      2 * ((i : ℤ) - (j : ℤ)) * x.2 =
        (x.1 - 2 * (j : ℤ) * x.2) - (x.1 - 2 * (i : ℤ) * x.2) := by
    ring
  have htri :
      |2 * ((i : ℤ) - (j : ℤ)) * x.2| ≤
        |x.1 - 2 * (j : ℤ) * x.2| + |x.1 - 2 * (i : ℤ) * x.2| := by
    rw [hid]
    exact abs_sub _ _
  dsimp [InCone] at hx
  omega

theorem step_into_cone (i : ℕ) (m : ℤ) (hm : m ≠ 0) (x : Label)
    (hx : |x.2| < |x.1 - 2 * (i : ℤ) * x.2|) :
    InCone i (step i m x) := by
  let c := x.1 - 2 * (i : ℤ) * x.2
  have hmabs : 1 ≤ |m| := by
    have := abs_pos.mpr hm
    omega
  have hlarge : 2 * |c| ≤ |2 * m * c| := by
    rw [abs_mul, abs_mul]
    norm_num
    have hp := mul_le_mul_of_nonneg_right hmabs (abs_nonneg c)
    have htwice := mul_le_mul_of_nonneg_left hp (show (0 : ℤ) ≤ 2 by omega)
    simpa only [mul_one, one_mul, mul_assoc] using htwice
  have htri : |2 * m * c| ≤ |x.2 + 2 * m * c| + |x.2| := by
    calc
      |2 * m * c| = |(x.2 + 2 * m * c) - x.2| := by congr 1; ring
      _ ≤ |x.2 + 2 * m * c| + |x.2| := abs_sub _ _
  have hbound : |c| < |x.2 + 2 * m * c| := by
    change |x.2| < |c| at hx
    omega
  have hfirst :
      (step i m x).1 - 2 * (i : ℤ) * (step i m x).2 = c := by
    dsimp [step, c]
    ring
  unfold InCone
  rw [hfirst]
  exact hbound

theorem step_other_cone (i j : ℕ) (hij : i ≠ j) (m : ℤ) (hm : m ≠ 0)
    (x : Label) (hx : InCone j x) : InCone i (step i m x) := by
  apply step_into_cone i m hm x
  exact other_cone j i (Ne.symm hij) x hx

def base : Label := (1, 0)

theorem base_not_in_cone (i : ℕ) : ¬ InCone i base := by
  simp [InCone, base]

theorem step_base_in_cone (i : ℕ) (m : ℤ) (hm : m ≠ 0) :
    InCone i (step i m base) := by
  apply step_into_cone i m hm base
  norm_num [base]

abbrev Syllable := ℕ × ℤ

def eval : List Syllable → Label → Label
  | [], x => x
  | (i, m) :: rest, x => step i m (eval rest x)

/-- A reduced word has nonzero exponents and distinct adjacent generator indices. -/
inductive Reduced : List Syllable → Prop
  | nil : Reduced []
  | single (i : ℕ) (m : ℤ) (hm : m ≠ 0) : Reduced [(i, m)]
  | cons (i j : ℕ) (m n : ℤ) (rest : List Syllable)
      (hm : m ≠ 0) (hij : i ≠ j) (htail : Reduced ((j, n) :: rest)) :
      Reduced ((i, m) :: (j, n) :: rest)

theorem reduced_eval_cone (word : List Syllable) (h : Reduced word) :
    match word with
    | [] => True
    | (i, _) :: _ => InCone i (eval word base) := by
  induction h with
  | nil => trivial
  | single i m hm => exact step_base_in_cone i m hm
  | cons i j m n rest hm hij htail ih =>
      exact step_other_cone i j hij m hm _ ih

/-- Every nonempty reduced word moves the particular integer label (1,0). -/
theorem nonempty_reduced_moves_base (word : List Syllable)
    (h : Reduced word) (hne : word ≠ []) : eval word base ≠ base := by
  cases word with
  | nil => exact False.elim (hne rfl)
  | cons syllable rest =>
      rcases syllable with ⟨i, m⟩
      have hc : InCone i (eval ((i, m) :: rest) base) := reduced_eval_cone _ h
      intro heq
      rw [heq] at hc
      exact base_not_in_cone i hc

/-- Explicit freeness: no nonempty reduced syllable word acts as the identity. -/
theorem nonempty_reduced_not_identity (word : List Syllable)
    (h : Reduced word) (hne : word ≠ []) : eval word ≠ id := by
  intro heq
  apply nonempty_reduced_moves_base word h hne
  exact congrFun heq base

/-- The usual product of integer powers of the generator permutations. -/
def wordPerm (word : List Syllable) : Equiv.Perm Label :=
  (word.map fun p => (stepPerm p.1 1) ^ p.2).prod

theorem wordPerm_apply (word : List Syllable) (x : Label) :
    wordPerm word x = eval word x := by
  induction word with
  | nil => rfl
  | cons syllable rest ih =>
      rcases syllable with ⟨i, m⟩
      simp only [wordPerm, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
        ← stepPerm_eq_zpow]
      simpa only [wordPerm, ← stepPerm_eq_zpow] using congrArg (step i m) ih

/-- Freeness expressed directly as a nonidentity product of permutation powers. -/
theorem reduced_product_ne_one (word : List Syllable)
    (h : Reduced word) (hne : word ≠ []) : wordPerm word ≠ 1 := by
  intro heq
  apply nonempty_reduced_moves_base word h hne
  rw [← wordPerm_apply, heq]
  rfl

end AdderCones


/-! Source component: MatrixGrowth.lean -/

namespace AdderTrace

abbrev IntMatrix2 := Matrix (Fin 2) (Fin 2) ℤ

/-- Maximum absolute row sum bounded by an integer. -/
def RowBound (X : IntMatrix2) (R : ℤ) : Prop :=
  ∀ i, |X i 0| + |X i 1| ≤ R

lemma rowBound_mul {X Y : IntMatrix2} {R S : ℤ}
    (hX : RowBound X R) (hY : RowBound Y S) (hS : 0 ≤ S) :
    RowBound (X * Y) (R * S) := by
  intro i
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  have h₀ := abs_add_le (X i 0 * Y 0 0) (X i 1 * Y 1 0)
  have h₁ := abs_add_le (X i 0 * Y 0 1) (X i 1 * Y 1 1)
  simp only [abs_mul] at h₀ h₁
  have hy₀ := mul_le_mul_of_nonneg_left (hY 0) (abs_nonneg (X i 0))
  have hy₁ := mul_le_mul_of_nonneg_left (hY 1) (abs_nonneg (X i 1))
  have hx := mul_le_mul_of_nonneg_right (hX i) hS
  nlinarith

lemma rowBound_one : RowBound (1 : IntMatrix2) 1 := by
  intro i
  fin_cases i <;> norm_num [Matrix.one_apply]

lemma rowBound_list_prod (xs : List IntMatrix2) (R : ℤ) (hR : 0 ≤ R)
    (hxs : ∀ X ∈ xs, RowBound X R) :
    RowBound xs.prod (R ^ xs.length) := by
  induction xs with
  | nil => simpa using rowBound_one
  | cons X xs ih =>
    have hx : RowBound X R := hxs X (by simp)
    have htail : ∀ Y ∈ xs, RowBound Y R := by
      intro Y hY
      exact hxs Y (by simp [hY])
    simpa [List.prod_cons, List.length_cons, pow_succ, mul_comm] using
      rowBound_mul hx (ih htail) (pow_nonneg hR xs.length)

/-- The block B^epsilon A^d for epsilon in {-1,1}. -/
def adderBlock (epsilon d : ℤ) : IntMatrix2 :=
  !![1, 2*d; 2*epsilon, 1+4*epsilon*d]

lemma adderBlock_rowBound (M : ℕ) (hM : 2 ≤ M) (epsilon d : ℤ)
    (he : |epsilon| = 1) (hd : |d| ≤ (M : ℤ) - 1) :
    RowBound (adderBlock epsilon d) (4*(M : ℤ)-1) := by
  have hM' : (2 : ℤ) ≤ M := by exact_mod_cast hM
  have hsum := abs_add_le (1 : ℤ) (4*epsilon*d)
  norm_num [abs_mul, he] at hsum
  intro i
  fin_cases i
  · change |(1 : ℤ)| + |2*d| ≤ 4*(M : ℤ)-1
    norm_num [abs_mul]
    omega
  · change |2*epsilon| + |1+4*epsilon*d| ≤ 4*(M : ℤ)-1
    norm_num [abs_mul, he]
    nlinarith

/-- A product of m permitted blocks has every absolute row sum <=(4M-1)^m. -/
theorem adderBlock_product_rowBound (M : ℕ) (hM : 2 ≤ M)
    (xs : List (ℤ × ℤ))
    (hxs : ∀ x ∈ xs, |x.1| = 1 ∧ |x.2| ≤ (M : ℤ)-1) :
    RowBound ((xs.map fun x => adderBlock x.1 x.2).prod)
      ((4*(M : ℤ)-1)^xs.length) := by
  have hM' : (2 : ℤ) ≤ M := by exact_mod_cast hM
  have h := rowBound_list_prod (xs.map fun x => adderBlock x.1 x.2)
      (4*(M : ℤ)-1) (by omega) ?_
  · simpa using h
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hX
    exact adderBlock_rowBound M hM x.1 x.2 (hxs x hx).1 (hxs x hx).2

/-- Subtracting the identity adds at most one to an entry bound. -/
theorem rowBound_sub_one_entry {X : IntMatrix2} {R : ℤ}
    (h : RowBound X R) (i j : Fin 2) : |(X - 1) i j| ≤ R + 1 := by
  have hij : |X i j| ≤ R := by
    fin_cases j
    · change |X i 0| ≤ R
      have := h i
      have := abs_nonneg (X i 1)
      omega
    · change |X i 1| ≤ R
      have := h i
      have := abs_nonneg (X i 0)
      omega
  have hone : |(1 : IntMatrix2) i j| ≤ 1 := by
    by_cases h : i = j
    · simp [Matrix.one_apply, h]
    · simp [Matrix.one_apply, h]
  calc
    |(X - 1) i j| = |X i j - (1 : IntMatrix2) i j| := rfl
    _ ≤ |X i j| + |(1 : IntMatrix2) i j| := by simpa using abs_sub_le (X i j) 0 ((1 : IntMatrix2) i j)
    _ ≤ R + 1 := add_le_add hij hone

/-- The explicit entry estimate with the exact B_L used in the proposition. -/
theorem adderBlock_product_entry_bound (M L : ℕ) (hM : 2 ≤ M)
    (xs : List (ℤ × ℤ)) (hlen : xs.length = 4*L)
    (hxs : ∀ x ∈ xs, |x.1| = 1 ∧ |x.2| ≤ (M : ℤ)-1)
    (i j : Fin 2) :
    (((xs.map fun x => adderBlock x.1 x.2).prod - 1) i j).natAbs ≤
      (4*M-1)^(4*L)+1 := by
  have h := rowBound_sub_one_entry (adderBlock_product_rowBound M hM xs hxs) i j
  rw [hlen] at h
  have hsub : (1 : ℕ) ≤ 4*M := by omega
  have hcast : ((4*M-1 : ℕ) : ℤ) = 4*(M : ℤ)-1 := by
    rw [Nat.cast_sub hsub]
    norm_num
  have h' : |(((xs.map fun x => adderBlock x.1 x.2).prod - 1) i j)| ≤
      (((4*M-1)^(4*L)+1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, hcast] using h
  rw [← Int.natCast_natAbs] at h'
  exact_mod_cast h'

/-- Integer lifts of the two adders. -/
def shearA (i : ℤ) : IntMatrix2 := !![1, 2*i; 0, 1]
def shearB (e : ℤ) : IntMatrix2 := !![1, 0; 2*e, 1]

lemma shearA_add (i j : ℤ) : shearA i * shearA j = shearA (i+j) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [shearA, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] lemma shearA_zero : shearA 0 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [shearA, Matrix.one_apply]

lemma shearB_mul_shearA (e d : ℤ) : shearB e * shearA d = adderBlock e d := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [shearA, shearB, adderBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- An arbitrary word in the conjugated adders and their inverses. -/
def conjugateWord (xs : List (ℤ × ℤ)) : IntMatrix2 :=
  (xs.map fun x => shearA x.1 * shearB x.2 * shearA (-x.1)).prod

def firstIndex (xs : List (ℤ × ℤ)) (finish : ℤ) : ℤ :=
  match xs with
  | [] => finish
  | x :: _ => x.1

def cyclicBlocks : List (ℤ × ℤ) → ℤ → List IntMatrix2
  | [], _ => []
  | x :: xs, finish =>
      adderBlock x.2 (firstIndex xs finish - x.1) :: cyclicBlocks xs finish

/-- Exact telescoping identity. The endpoint conjugation is explicit. -/
lemma conjugateWord_telescope (xs : List (ℤ × ℤ)) (start finish : ℤ) :
    shearA (-start) * conjugateWord xs * shearA finish =
      shearA (firstIndex xs finish - start) * (cyclicBlocks xs finish).prod := by
  induction xs generalizing start with
  | nil =>
    simp [conjugateWord, cyclicBlocks, firstIndex, shearA_add, sub_eq_add_neg, add_comm]
  | cons x xs ih =>
    have ha : shearA (-start) * shearA x.1 = shearA (x.1-start) := by
      rw [shearA_add]
      congr 1
      ring
    calc
      shearA (-start) * conjugateWord (x::xs) * shearA finish =
          (shearA (-start) * shearA x.1) * shearB x.2 *
          (shearA (-x.1) * conjugateWord xs * shearA finish) := by
        simp only [conjugateWord, List.map_cons, List.prod_cons, mul_assoc]
      _ = shearA (x.1-start) * shearB x.2 *
          (shearA (firstIndex xs finish-x.1) * (cyclicBlocks xs finish).prod) := by
        rw [ha, ih]
      _ = shearA (firstIndex (x::xs) finish-start) *
          (cyclicBlocks (x::xs) finish).prod := by
        simp only [firstIndex, cyclicBlocks, List.prod_cons, ← shearB_mul_shearA, mul_assoc]

lemma firstIndex_range (M : ℕ) (xs : List (ℤ × ℤ)) (finish : ℤ)
    (hf : 0 ≤ finish ∧ finish ≤ (M:ℤ)-1)
    (hx : ∀ x ∈ xs, 0 ≤ x.1 ∧ x.1 ≤ (M:ℤ)-1) :
    0 ≤ firstIndex xs finish ∧ firstIndex xs finish ≤ (M:ℤ)-1 := by
  cases xs with
  | nil => exact hf
  | cons x xs => exact hx x (by simp)

lemma cyclicBlocks_rowBound (M : ℕ) (hM : 2 ≤ M)
    (xs : List (ℤ × ℤ)) (finish : ℤ)
    (hf : 0 ≤ finish ∧ finish ≤ (M:ℤ)-1)
    (hx : ∀ x ∈ xs, |x.2| = 1 ∧ 0 ≤ x.1 ∧ x.1 ≤ (M:ℤ)-1) :
    RowBound (cyclicBlocks xs finish).prod ((4*(M:ℤ)-1)^xs.length) := by
  have hM' : (2:ℤ) ≤ M := by exact_mod_cast hM
  induction xs with
  | nil => simpa [cyclicBlocks] using rowBound_one
  | cons x xs ih =>
    have hx₀ := hx x (by simp)
    have htail : ∀ y ∈ xs, |y.2| = 1 ∧ 0 ≤ y.1 ∧ y.1 ≤ (M:ℤ)-1 := by
      intro y hy
      exact hx y (by simp [hy])
    have hnext := firstIndex_range M xs finish hf (fun y hy => (htail y hy).2)
    have hdiff : |firstIndex xs finish-x.1| ≤ (M:ℤ)-1 := by
      rw [abs_le]
      omega
    have hb := adderBlock_rowBound M hM x.2 (firstIndex xs finish-x.1) hx₀.1 hdiff
    have hh := rowBound_mul hb (ih htail) (pow_nonneg (by omega) xs.length)
    simpa [cyclicBlocks, List.prod_cons, List.length_cons, pow_succ, mul_comm] using hh

/-- Every conjugated-adder word admits a cyclic conjugation with the claimed
row bound. This supplies the actual entry-growth step, not a hypothesis. -/
theorem cyclic_conjugation_rowBound (M : ℕ) (hM : 2 ≤ M)
    (xs : List (ℤ × ℤ))
    (hx : ∀ x ∈ xs, |x.2| = 1 ∧ 0 ≤ x.1 ∧ x.1 ≤ (M:ℤ)-1) :
    RowBound (shearA (-firstIndex xs 0) * conjugateWord xs * shearA (firstIndex xs 0))
      ((4*(M:ℤ)-1)^xs.length) := by
  have hM' : (2:ℤ) ≤ M := by exact_mod_cast hM
  have hstart := firstIndex_range M xs 0 (by omega) (fun x h => (hx x h).2)
  have hsame : firstIndex xs (firstIndex xs 0) = firstIndex xs 0 := by
    cases xs <;> rfl
  rw [conjugateWord_telescope, hsame, sub_self, shearA_zero, one_mul]
  exact cyclicBlocks_rowBound M hM xs (firstIndex xs 0) hstart hx

/-- The entry estimate B_L for the actual cyclic conjugation of a length-4L word. -/
theorem cyclic_conjugation_entry_bound (M L : ℕ) (hM : 2 ≤ M)
    (xs : List (ℤ × ℤ)) (hlen : xs.length = 4*L)
    (hx : ∀ x ∈ xs, |x.2| = 1 ∧ 0 ≤ x.1 ∧ x.1 ≤ (M:ℤ)-1)
    (i j : Fin 2) :
    ((shearA (-firstIndex xs 0) * conjugateWord xs * shearA (firstIndex xs 0)-1) i j).natAbs
      ≤ (4*M-1)^(4*L)+1 := by
  have h := rowBound_sub_one_entry (cyclic_conjugation_rowBound M hM xs hx) i j
  rw [hlen] at h
  have hsub : (1 : ℕ) ≤ 4*M := by omega
  have hcast : ((4*M-1 : ℕ) : ℤ) = 4*(M : ℤ)-1 := by
    rw [Nat.cast_sub hsub]
    norm_num
  have h' : |((shearA (-firstIndex xs 0) * conjugateWord xs * shearA (firstIndex xs 0)-1) i j)| ≤
      (((4*M-1)^(4*L)+1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, hcast] using h
  rw [← Int.natCast_natAbs] at h'
  exact_mod_cast h'

end AdderTrace


/-! Source component: AdderMatrixBridge.lean -/

/-! The cone proof and the matrix-growth proof describe exactly the same
integer adder words.  This module checks that identification. -/

namespace AdderTrace

def matrixAction (X : IntMatrix2) (x : AdderCones.Label) : AdderCones.Label :=
  (X 0 0 * x.1 + X 0 1 * x.2, X 1 0 * x.1 + X 1 1 * x.2)

theorem matrixAction_mul (X Y : IntMatrix2) (x : AdderCones.Label) :
    matrixAction (X * Y) x = matrixAction X (matrixAction Y x) := by
  apply Prod.ext <;>
    simp [matrixAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem matrixAction_one (x : AdderCones.Label) : matrixAction 1 x = x := by
  simp [matrixAction]

theorem matrixAction_shearA (i : ℤ) (x : AdderCones.Label) :
    matrixAction (shearA i) x = AdderCones.upper i x := by
  simp [matrixAction, shearA, AdderCones.upper]

theorem matrixAction_shearB (m : ℤ) (x : AdderCones.Label) :
    matrixAction (shearB m) x = AdderCones.lower m x := by
  simp [matrixAction, shearB, AdderCones.lower, add_comm]

def liftWord (word : List AdderCones.Syllable) : List (ℤ × ℤ) :=
  word.map fun p => ((p.1 : ℤ), p.2)

theorem conjugateWord_action (word : List AdderCones.Syllable)
    (x : AdderCones.Label) :
    matrixAction (conjugateWord (liftWord word)) x = AdderCones.eval word x := by
  induction word generalizing x with
  | nil =>
      simpa [liftWord, conjugateWord, AdderCones.eval] using matrixAction_one x
  | cons syllable rest ih =>
      rcases syllable with ⟨i, m⟩
      change matrixAction
          ((shearA (i : ℤ) * shearB m * shearA (-(i : ℤ))) *
            conjugateWord (liftWord rest)) x =
        AdderCones.step i m (AdderCones.eval rest x)
      rw [matrixAction_mul, ih, matrixAction_mul, matrixAction_mul,
        matrixAction_shearA, matrixAction_shearB, matrixAction_shearA]
      exact (AdderCones.step_eq_conjugate i m _).symm

/-- Freeness of the concrete integer matrices, obtained from the checked
cone proof and the checked matrix-action identification. -/
theorem reduced_conjugateWord_ne_one (word : List AdderCones.Syllable)
    (h : AdderCones.Reduced word) (hne : word ≠ []) :
    conjugateWord (liftWord word) ≠ 1 := by
  intro heq
  apply AdderCones.nonempty_reduced_moves_base word h hne
  rw [← conjugateWord_action, heq, matrixAction_one]

theorem shear_conjugation_ne_one (X : IntMatrix2) (s : ℤ) (hX : X ≠ 1) :
    shearA (-s) * X * shearA s ≠ 1 := by
  intro heq
  apply hX
  calc
    X = (shearA s * shearA (-s)) * X * (shearA s * shearA (-s)) := by
      simp [shearA_add]
    _ = shearA s * (shearA (-s) * X * shearA s) * shearA (-s) := by
      simp only [mul_assoc]
    _ = shearA s * 1 * shearA (-s) := by rw [heq]
    _ = 1 := by simp [shearA_add]

theorem reduced_cyclic_conjugation_ne_one (word : List AdderCones.Syllable)
    (h : AdderCones.Reduced word) (hne : word ≠ []) :
    shearA (-firstIndex (liftWord word) 0) * conjugateWord (liftWord word) *
      shearA (firstIndex (liftWord word) 0) ≠ 1 := by
  exact shear_conjugation_ne_one _ _ (reduced_conjugateWord_ne_one word h hne)

#print axioms reduced_conjugateWord_ne_one
#print axioms reduced_cyclic_conjugation_ne_one

end AdderTrace


/-! Source component: AdderFreeGroup.lean -/

/-! Injectivity of the actual universal free-group representation. -/

namespace AdderCones

def freeRepresentation : FreeGroup ℕ →* Equiv.Perm Label :=
  FreeGroup.lift fun i => stepPerm i 1

/-- The family of integer conjugated adders is a faithful representation
of the free group, using the elementary cones proved in `AdderCones`. -/
theorem freeRepresentation_injective : Function.Injective freeRepresentation := by
  classical
  let f : ∀ _i : ℕ, FreeGroup Unit →* Equiv.Perm Label :=
    fun i => FreeGroup.lift fun _ => stepPerm i 1
  have hf : Function.Injective (Monoid.CoprodI.lift f) := by
    apply Monoid.CoprodI.lift_injective_of_ping_pong f
      (Or.inl (by simpa using (Cardinal.nat_lt_aleph0 3).le))
      (fun i => {x : Label | InCone i x})
    · intro i
      refine ⟨(2 * (i : ℤ), 1), ?_⟩
      simp [InCone]
    · intro i j hij
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      have h := other_cone i j hij x hxi
      exact (not_lt_of_gt h) hxj
    · intro i j hij h hne
      rintro _ ⟨x, hx, rfl⟩
      let m : ℤ := FreeGroup.freeGroupUnitEquivInt h
      have hh : (FreeGroup.of () : FreeGroup Unit) ^ m = h :=
        FreeGroup.freeGroupUnitEquivInt.symm_apply_apply h
      have hm : m ≠ 0 := by
        intro hm
        apply hne
        rw [← hh, hm, zpow_zero]
      have hpow : f i h = stepPerm i m := by
        rw [← hh, map_zpow]
        change (stepPerm i 1) ^ m = stepPerm i m
        exact (stepPerm_eq_zpow i m).symm
      change InCone i ((f i h) x)
      rw [hpow]
      exact step_other_cone i j hij m hm x hx
  have heq : freeRepresentation =
      (Monoid.CoprodI.lift f).comp (@freeGroupEquivCoprodI ℕ).toMonoidHom := by
    apply FreeGroup.ext_hom
    intro i
    simp [freeRepresentation, f]
  rw [heq, MonoidHom.coe_comp]
  exact hf.comp freeGroupEquivCoprodI.injective

theorem freeRepresentation_ne_one {g : FreeGroup ℕ} (hg : g ≠ 1) :
    freeRepresentation g ≠ 1 := by
  intro h
  apply hg
  apply freeRepresentation_injective
  simpa using h

def freeWord (word : List Syllable) : FreeGroup ℕ :=
  (word.map fun p => (FreeGroup.of p.1) ^ p.2).prod

theorem freeRepresentation_freeWord (word : List Syllable) :
    freeRepresentation (freeWord word) = wordPerm word := by
  simp [freeWord, wordPerm, freeRepresentation, map_list_prod, List.map_map, Function.comp_def, map_zpow]

#print axioms freeRepresentation_injective
#print axioms freeRepresentation_ne_one

end AdderCones

namespace AdderTrace

/-- The integer word is nonidentity whenever its abstract free-group
word is nonidentity, with no reduced-normal-form assumption. -/
theorem freeWord_conjugateWord_ne_one (word : List AdderCones.Syllable)
    (hfree : AdderCones.freeWord word ≠ 1) :
    conjugateWord (liftWord word) ≠ 1 := by
  intro hmatrix
  apply AdderCones.freeRepresentation_ne_one hfree
  apply Equiv.ext
  intro x
  rw [AdderCones.freeRepresentation_freeWord, AdderCones.wordPerm_apply,
    ← conjugateWord_action, hmatrix, matrixAction_one]
  rfl

#print axioms freeWord_conjugateWord_ne_one

end AdderTrace


/-! Source component: FixedLabels.lean -/

/-!
Elementary fixed-label counting, independent of any free-group or operator-norm
estimate. The proof embeds a congruence fiber into a quotient interval.
-/
namespace AdderTrace

/-- Equal multiplication by an integer implies equal multiplication by its
absolute value, also over rings with zero divisors. -/
lemma natAbs_mul_eq_of_int_mul_eq {R : Type*} [Ring R]
    (d : ℤ) {x y : R} (h : (d : R) * x = (d : R) * y) :
    (d.natAbs : R) * x = (d.natAbs : R) * y := by
  cases d with
  | ofNat n => simpa using h
  | negSucc n =>
    simpa only [Int.natAbs_negSucc, Int.cast_negSucc, neg_mul, neg_inj] using h

/-- Direct fixed-label counting: one nonzero integer coefficient gives at most
`Q * |d|` solutions to a linear equation modulo Q. This holds for every positive
modulus, not just powers of two. -/
theorem linear_congruence_card_le (Q : ℕ) [NeZero Q]
    (d e : ℤ) (hd : d ≠ 0) :
    Fintype.card {x : ZMod Q × ZMod Q //
      (d : ZMod Q) * x.1 + (e : ZMod Q) * x.2 = 0}
      ≤ Q * d.natAbs := by
  classical
  have hQ : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hdpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd
  let S := {x : ZMod Q × ZMod Q //
      (d : ZMod Q) * x.1 + (e : ZMod Q) * x.2 = 0}
  let f : S → Fin d.natAbs × ZMod Q := fun x =>
    (⟨(d.natAbs * x.1.1.val) / Q, by
      apply (Nat.div_lt_iff_lt_mul hQ).2
      exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x.1.1) hdpos⟩, x.1.2)
  have hf : Function.Injective f := by
    intro x y hxy
    have hsecond : x.1.2 = y.1.2 := congrArg (fun p : Fin d.natAbs × ZMod Q => p.2) hxy
    have hquot : d.natAbs * x.1.1.val / Q =
        d.natAbs * y.1.1.val / Q :=
      congrArg (fun p : Fin d.natAbs × ZMod Q => p.1.val) hxy
    have hint : (d : ZMod Q) * x.1.1 = (d : ZMod Q) * y.1.1 := by
      have hx := x.2
      have hy := y.2
      rw [hsecond] at hx
      exact add_right_cancel (hx.trans hy.symm)
    have habs := natAbs_mul_eq_of_int_mul_eq d hint
    have hmod : (d.natAbs * x.1.1.val) % Q =
        (d.natAbs * y.1.1.val) % Q := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ Q).mp
      simpa only [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id] using habs
    have hprod : d.natAbs * x.1.1.val = d.natAbs * y.1.1.val := by
      calc
        d.natAbs * x.1.1.val =
            (d.natAbs * x.1.1.val) % Q + Q * ((d.natAbs * x.1.1.val) / Q) :=
          (Nat.mod_add_div _ _).symm
        _ = (d.natAbs * y.1.1.val) % Q + Q * ((d.natAbs * y.1.1.val) / Q) := by
          rw [hmod, hquot]
        _ = d.natAbs * y.1.1.val := Nat.mod_add_div _ _
    apply Subtype.ext
    apply Prod.ext
    · apply ZMod.val_injective Q
      exact Nat.eq_of_mul_eq_mul_left hdpos hprod
    · exact hsecond
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [S, Fintype.card_prod, Fintype.card_fin, ZMod.card, Nat.mul_comm] using hcard

/-- The same count when the nonzero coefficient is in the second column. -/
theorem linear_congruence_card_le_right (Q : ℕ) [NeZero Q]
    (d e : ℤ) (he : e ≠ 0) :
    Fintype.card {x : ZMod Q × ZMod Q //
      (d : ZMod Q) * x.1 + (e : ZMod Q) * x.2 = 0}
      ≤ Q * e.natAbs := by
  classical
  let f : {x : ZMod Q × ZMod Q //
      (d : ZMod Q) * x.1 + (e : ZMod Q) * x.2 = 0} →
      {x : ZMod Q × ZMod Q //
      (e : ZMod Q) * x.1 + (d : ZMod Q) * x.2 = 0} :=
    fun x => ⟨(x.1.2, x.1.1), by simpa [add_comm] using x.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact Prod.swap_injective (congrArg Subtype.val h)
  exact (Fintype.card_le_of_injective f hf).trans
    (linear_congruence_card_le Q e d he)

/-- Fixed labels of the integer matrix with entries a,b,c,d, reduced modulo Q. -/
def MatrixFixedLabels (Q : ℕ) (a b c d : ℤ) :=
  {x : ZMod Q × ZMod Q //
    (a : ZMod Q) * x.1 + (b : ZMod Q) * x.2 = x.1 ∧
    (c : ZMod Q) * x.1 + (d : ZMod Q) * x.2 = x.2}

noncomputable instance (Q : ℕ) [NeZero Q] (a b c d : ℤ) :
    Fintype (MatrixFixedLabels Q a b c d) := by
  unfold MatrixFixedLabels
  infer_instance

/-- A nonidentity integer 2x2 matrix whose entries after subtracting the identity
have absolute value at most B fixes at most QB labels modulo Q. -/
theorem matrix_fixed_card_le (Q B : ℕ) [NeZero Q] (a b c d : ℤ)
    (hne : a ≠ 1 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 1)
    (ha : (a - 1).natAbs ≤ B) (hb : b.natAbs ≤ B)
    (hc : c.natAbs ≤ B) (hd : (d - 1).natAbs ≤ B) :
    Fintype.card (MatrixFixedLabels Q a b c d) ≤ Q * B := by
  classical
  have hrow1 : Fintype.card (MatrixFixedLabels Q a b c d) ≤
      Fintype.card {x : ZMod Q × ZMod Q //
        ((a - 1 : ℤ) : ZMod Q) * x.1 + (b : ZMod Q) * x.2 = 0} := by
    apply Fintype.card_le_of_injective
      (fun x : MatrixFixedLabels Q a b c d =>
        (⟨x.1, by
          have hx := x.2.1
          simp only [Int.cast_sub, Int.cast_one]
          linear_combination hx⟩ : {x : ZMod Q × ZMod Q //
            ((a - 1 : ℤ) : ZMod Q) * x.1 + (b : ZMod Q) * x.2 = 0}))
    intro x y h
    have hh := congrArg Subtype.val h
    exact Subtype.ext hh
  have hrow2 : Fintype.card (MatrixFixedLabels Q a b c d) ≤
      Fintype.card {x : ZMod Q × ZMod Q //
        (c : ZMod Q) * x.1 + ((d - 1 : ℤ) : ZMod Q) * x.2 = 0} := by
    apply Fintype.card_le_of_injective
      (fun x : MatrixFixedLabels Q a b c d =>
        (⟨x.1, by
          have hx := x.2.2
          simp only [Int.cast_sub, Int.cast_one]
          linear_combination hx⟩ : {x : ZMod Q × ZMod Q //
            (c : ZMod Q) * x.1 + ((d - 1 : ℤ) : ZMod Q) * x.2 = 0}))
    intro x y h
    have hh := congrArg Subtype.val h
    exact Subtype.ext hh
  rcases hne with h | h | h | h
  · exact hrow1.trans ((linear_congruence_card_le Q (a - 1) b (sub_ne_zero.mpr h)).trans
      (Nat.mul_le_mul_left Q ha))
  · exact hrow1.trans ((linear_congruence_card_le_right Q (a - 1) b h).trans
      (Nat.mul_le_mul_left Q hb))
  · exact hrow2.trans ((linear_congruence_card_le Q c (d - 1) h).trans
      (Nat.mul_le_mul_left Q hc))
  · exact hrow2.trans ((linear_congruence_card_le_right Q c (d - 1) (sub_ne_zero.mpr h)).trans
      (Nat.mul_le_mul_left Q hd))

/-- The normalized form used in the trace estimate. -/
theorem matrix_fixed_fraction_le (Q B : ℕ) [NeZero Q] (a b c d : ℤ)
    (hne : a ≠ 1 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 1)
    (ha : (a - 1).natAbs ≤ B) (hb : b.natAbs ≤ B)
    (hc : c.natAbs ≤ B) (hd : (d - 1).natAbs ≤ B) :
    (Fintype.card (MatrixFixedLabels Q a b c d) : ℝ) / (Q : ℝ)^2 ≤ B / Q := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hcard : (Fintype.card (MatrixFixedLabels Q a b c d) : ℝ) ≤ Q * B := by
    exact_mod_cast matrix_fixed_card_le Q B a b c d hne ha hb hc hd
  apply (div_le_iff₀ (sq_pos_of_pos hQ)).2
  calc
    (Fintype.card (MatrixFixedLabels Q a b c d) : ℝ) ≤ Q * B := hcard
    _ = B / (Q : ℝ) * (Q : ℝ)^2 := by
      field_simp

end AdderTrace


/-! Source component: FixedWordBound.lean -/

namespace AdderTrace

/-- The action of an integer matrix on the computational labels modulo Q. -/
def labelAction (Q : ℕ) (X : IntMatrix2) (x : ZMod Q × ZMod Q) : ZMod Q × ZMod Q :=
  ((X 0 0 : ZMod Q)*x.1 + (X 0 1 : ZMod Q)*x.2,
   (X 1 0 : ZMod Q)*x.1 + (X 1 1 : ZMod Q)*x.2)

lemma labelAction_mul (Q : ℕ) (X Y : IntMatrix2) (x : ZMod Q × ZMod Q) :
    labelAction Q (X*Y) x = labelAction Q X (labelAction Q Y x) := by
  apply Prod.ext <;>
    simp [labelAction, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] lemma labelAction_one (Q : ℕ) (x : ZMod Q × ZMod Q) :
    labelAction Q 1 x = x := by
  apply Prod.ext <;> simp [labelAction, Matrix.one_apply]

/-- Shear conjugation does not change the number of fixed labels. -/
def shearFixedEquiv (Q : ℕ) (X : IntMatrix2) (s : ℤ) :
    {x : ZMod Q × ZMod Q //
      labelAction Q (shearA (-s)*X*shearA s) x = x} ≃
    {x : ZMod Q × ZMod Q // labelAction Q X x = x} where
  toFun x := ⟨labelAction Q (shearA s) x.1, by
    have hh := congrArg (labelAction Q (shearA s)) x.2
    have he : shearA s * (shearA (-s)*X*shearA s) = X*shearA s := by
      calc
        shearA s * (shearA (-s)*X*shearA s) =
            (shearA s * shearA (-s))*X*shearA s := by simp only [mul_assoc]
        _ = X*shearA s := by rw [shearA_add, add_neg_cancel, shearA_zero, one_mul]
    rw [← labelAction_mul, he, labelAction_mul] at hh
    exact hh⟩
  invFun x := ⟨labelAction Q (shearA (-s)) x.1, by
    have he : (shearA (-s)*X*shearA s)*shearA (-s) = shearA (-s)*X := by
      calc
        (shearA (-s)*X*shearA s)*shearA (-s) =
            shearA (-s)*X*(shearA s*shearA (-s)) := by simp only [mul_assoc]
        _ = shearA (-s)*X := by rw [shearA_add, add_neg_cancel, shearA_zero, mul_one]
    rw [← labelAction_mul, he, labelAction_mul, x.2]⟩
  left_inv x := by
    apply Subtype.ext
    change labelAction Q (shearA (-s)) (labelAction Q (shearA s) x.1) = x.1
    rw [← labelAction_mul, shearA_add, neg_add_cancel, shearA_zero, labelAction_one]
  right_inv x := by
    apply Subtype.ext
    change labelAction Q (shearA s) (labelAction Q (shearA (-s)) x.1) = x.1
    rw [← labelAction_mul, shearA_add, add_neg_cancel, shearA_zero, labelAction_one]

lemma shear_conjugate_ne_one (X : IntMatrix2) (hX : X ≠ 1) (s : ℤ) :
    shearA (-s)*X*shearA s ≠ 1 := by
  intro h
  apply hX
  have hh := congrArg (fun Y : IntMatrix2 => shearA s*Y*shearA (-s)) h
  have hl : shearA s*(shearA (-s)*X*shearA s)*shearA (-s) = X := by
    calc
      shearA s*(shearA (-s)*X*shearA s)*shearA (-s) =
          (shearA s*shearA (-s))*X*(shearA s*shearA (-s)) := by simp only [mul_assoc]
      _ = X := by rw [shearA_add, add_neg_cancel, shearA_zero, one_mul, mul_one]
  dsimp only at hh
  rw [hl] at hh
  simpa [shearA_add] using hh

/-- The pair-equation and scalar-equation descriptions of fixed labels agree. -/
def fixedLabelsEquiv (Q : ℕ) (X : IntMatrix2) :
    {x : ZMod Q × ZMod Q // labelAction Q X x = x} ≃
      MatrixFixedLabels Q (X 0 0) (X 0 1) (X 1 0) (X 1 1) where
  toFun x := ⟨x.1, ⟨congrArg Prod.fst x.2, congrArg Prod.snd x.2⟩⟩
  invFun x := ⟨x.1, Prod.ext x.2.1 x.2.2⟩
  left_inv x := rfl
  right_inv x := rfl

lemma matrix_ne_one_entries (X : IntMatrix2) (hX : X ≠ 1) :
    X 0 0 ≠ 1 ∨ X 0 1 ≠ 0 ∨ X 1 0 ≠ 0 ∨ X 1 1 ≠ 1 := by
  by_contra h
  push_neg at h
  apply hX
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h]

/-- Full fixed-label bound for a word, assuming only its integer lift is
nonidentity. Freeness is a separate theorem supplying that hypothesis. -/
theorem nonidentity_word_fixed_card_le (Q M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (xs : List (ℤ × ℤ)) (hlen : xs.length = 4*L)
    (hx : ∀ x ∈ xs, |x.2| = 1 ∧ 0 ≤ x.1 ∧ x.1 ≤ (M:ℤ)-1)
    (hne : conjugateWord xs ≠ 1) :
    Fintype.card {x : ZMod Q × ZMod Q // labelAction Q (conjugateWord xs) x = x}
      ≤ Q*((4*M-1)^(4*L)+1) := by
  classical
  let H := shearA (-firstIndex xs 0)*conjugateWord xs*shearA (firstIndex xs 0)
  have hH : H ≠ 1 := shear_conjugate_ne_one _ hne _
  have hb (i j : Fin 2) : ((H-1) i j).natAbs ≤ (4*M-1)^(4*L)+1 :=
    cyclic_conjugation_entry_bound M L hM xs hlen hx i j
  have hcard := matrix_fixed_card_le Q ((4*M-1)^(4*L)+1)
      (H 0 0) (H 0 1) (H 1 0) (H 1 1) (matrix_ne_one_entries H hH)
      (by simpa [Matrix.sub_apply, Matrix.one_apply] using hb 0 0)
      (by simpa [Matrix.sub_apply, Matrix.one_apply] using hb 0 1)
      (by simpa [Matrix.sub_apply, Matrix.one_apply] using hb 1 0)
      (by simpa [Matrix.sub_apply, Matrix.one_apply] using hb 1 1)
  have hc₁ := Fintype.card_congr (shearFixedEquiv Q (conjugateWord xs) (firstIndex xs 0))
  have hc₂ := Fintype.card_congr (fixedLabelsEquiv Q H)
  change Fintype.card {x : ZMod Q × ZMod Q // labelAction Q H x = x} = _ at hc₁
  rw [← hc₁, hc₂]
  exact hcard

/-- Normalized fixed-label bound B_L/Q for the original word, after transferring
back from its cyclic conjugation. -/
theorem nonidentity_word_fixed_fraction_le (Q M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (xs : List (ℤ × ℤ)) (hlen : xs.length = 4*L)
    (hx : ∀ x ∈ xs, |x.2| = 1 ∧ 0 ≤ x.1 ∧ x.1 ≤ (M:ℤ)-1)
    (hne : conjugateWord xs ≠ 1) :
    (Fintype.card {x : ZMod Q × ZMod Q // labelAction Q (conjugateWord xs) x = x} : ℝ)
      / (Q:ℝ)^2 ≤ ((4*M-1)^(4*L)+1 : ℕ) / (Q:ℝ) := by
  have hQ : (0:ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hc : (Fintype.card {x : ZMod Q × ZMod Q // labelAction Q (conjugateWord xs) x = x} : ℝ)
      ≤ (Q:ℝ)*(((4*M-1)^(4*L)+1 : ℕ):ℝ) := by
    exact_mod_cast nonidentity_word_fixed_card_le Q M L hM xs hlen hx hne
  apply (div_le_iff₀ (sq_pos_of_pos hQ)).2
  calc
    _ ≤ (Q:ℝ)*(((4*M-1)^(4*L)+1 : ℕ):ℝ) := hc
    _ = (((4*M-1)^(4*L)+1 : ℕ):ℝ)/(Q:ℝ)*(Q:ℝ)^2 := by field_simp

end AdderTrace


/-! Source component: FreeWordTrace.lean -/

namespace AdderTrace

/-- The exact B_L/Q fixed-label bound for every abstractly nontrivial
length-4L word, without any reduced-normal-form restriction. -/
theorem free_nontrivial_word_fixed_fraction_le (Q M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (word : List AdderCones.Syllable)
    (hfree : AdderCones.freeWord word ≠ 1) (hlen : word.length = 4 * L)
    (hletters : ∀ p ∈ word, |p.2| = 1 ∧ p.1 < M) :
    (Fintype.card {x : ZMod Q × ZMod Q //
      labelAction Q (conjugateWord (liftWord word)) x = x} : ℝ) / (Q : ℝ) ^ 2 ≤
      ((4 * M - 1) ^ (4 * L) + 1 : ℕ) / (Q : ℝ) := by
  apply nonidentity_word_fixed_fraction_le Q M L hM (liftWord word)
  · simpa [liftWord] using hlen
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hi : (p.1 : ℤ) < M := by exact_mod_cast (hletters p hp).2
    exact ⟨(hletters p hp).1, by omega, by omega⟩
  · exact freeWord_conjugateWord_ne_one word hfree

#print axioms free_nontrivial_word_fixed_fraction_le

end AdderTrace


/-! Source component: ModularRepresentation.lean -/

/-! The explicit integer adders act as permutations of the modular labels.
Their universal free-group representation is identified with the integer
matrix word reduced modulo Q. -/

namespace AdderTrace

lemma shearB_add (s t : ℤ) : shearB s * shearB t = shearB (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [shearB, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

@[simp] lemma shearB_zero : shearB 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [shearB, Matrix.one_apply]

def conjugatedShear (i : ℕ) (m : ℤ) : IntMatrix2 :=
  shearA (i : ℤ) * shearB m * shearA (-(i : ℤ))

lemma conjugatedShear_add (i : ℕ) (s t : ℤ) :
    conjugatedShear i s * conjugatedShear i t = conjugatedShear i (s + t) := by
  calc
    _ = shearA (i : ℤ) * shearB s *
        (shearA (-(i : ℤ)) * shearA (i : ℤ)) * shearB t * shearA (-(i : ℤ)) := by
      simp only [conjugatedShear, mul_assoc]
    _ = conjugatedShear i (s + t) := by
      rw [shearA_add, neg_add_cancel, shearA_zero]
      simp only [mul_one, conjugatedShear, mul_assoc, shearB_add]

@[simp] lemma conjugatedShear_zero (i : ℕ) : conjugatedShear i 0 = 1 := by
  simp [conjugatedShear, shearA_add]

def modularStepPerm (Q i : ℕ) (m : ℤ) : Equiv.Perm (ZMod Q × ZMod Q) where
  toFun := labelAction Q (conjugatedShear i m)
  invFun := labelAction Q (conjugatedShear i (-m))
  left_inv x := by
    rw [← labelAction_mul, conjugatedShear_add, neg_add_cancel,
      conjugatedShear_zero, labelAction_one]
  right_inv x := by
    rw [← labelAction_mul, conjugatedShear_add, add_neg_cancel,
      conjugatedShear_zero, labelAction_one]

def modularStepHom (Q i : ℕ) : Multiplicative ℤ →* Equiv.Perm (ZMod Q × ZMod Q) where
  toFun m := modularStepPerm Q i m.toAdd
  map_one' := by
    apply Equiv.ext
    intro x
    change labelAction Q (conjugatedShear i 0) x = x
    rw [conjugatedShear_zero, labelAction_one]
  map_mul' s t := by
    apply Equiv.ext
    intro x
    change labelAction Q (conjugatedShear i (s.toAdd + t.toAdd)) x =
      labelAction Q (conjugatedShear i s.toAdd)
        (labelAction Q (conjugatedShear i t.toAdd) x)
    rw [← labelAction_mul, conjugatedShear_add]

theorem modularStepPerm_eq_zpow (Q i : ℕ) (m : ℤ) :
    modularStepPerm Q i m = (modularStepPerm Q i 1) ^ m := by
  have h := map_zpow (modularStepHom Q i) (Multiplicative.ofAdd (1 : ℤ)) m
  simpa [modularStepHom, toAdd_zpow] using h

def modularRepresentation (Q : ℕ) : FreeGroup ℕ →* Equiv.Perm (ZMod Q × ZMod Q) :=
  FreeGroup.lift fun i => modularStepPerm Q i 1

@[simp] theorem modularRepresentation_of (Q i : ℕ) :
    modularRepresentation Q (FreeGroup.of i) = modularStepPerm Q i 1 := by
  simp [modularRepresentation]

/-- Equality between the actual permutation representation and reduction
modulo Q of the integer matrix product. -/
theorem modularRepresentation_freeWord_apply (Q : ℕ)
    (word : List AdderCones.Syllable) (x : ZMod Q × ZMod Q) :
    modularRepresentation Q (AdderCones.freeWord word) x =
      labelAction Q (conjugateWord (liftWord word)) x := by
  induction word with
  | nil =>
      simp [AdderCones.freeWord, liftWord, conjugateWord, labelAction_one]
  | cons p rest ih =>
      change modularRepresentation Q
          ((FreeGroup.of p.1) ^ p.2 * AdderCones.freeWord rest) x =
        labelAction Q (conjugatedShear p.1 p.2 * conjugateWord (liftWord rest)) x
      rw [map_mul, map_zpow, modularRepresentation_of, ← modularStepPerm_eq_zpow,
        Equiv.Perm.mul_apply, ih, labelAction_mul]
      rfl

/-- Exact normalized fixed-label estimate for the genuine modular
permutation representation of every nontrivial length-4L word. -/
theorem modular_word_fixedRatio_le (Q M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (word : List AdderCones.Syllable)
    (hfree : AdderCones.freeWord word ≠ 1) (hlen : word.length = 4 * L)
    (hletters : ∀ p ∈ word, |p.2| = 1 ∧ p.1 < M) :
    (Fintype.card {x : ZMod Q × ZMod Q //
      modularRepresentation Q (AdderCones.freeWord word) x = x} : ℝ) / (Q : ℝ) ^ 2 ≤
      ((4 * M - 1) ^ (4 * L) + 1 : ℕ) / (Q : ℝ) := by
  simpa only [modularRepresentation_freeWord_apply] using
    free_nontrivial_word_fixed_fraction_le Q M L hM word hfree hlen hletters

#print axioms modularRepresentation_freeWord_apply
#print axioms modular_word_fixedRatio_le

end AdderTrace


/-! Source component: PermutationMoments.lean -/

/-!
# Permutation matrices and fixed labels

An elementary bridge from actual matrix traces to fixed-label counts.
No operator-norm or spectral hypotheses occur in these lemmas.
-/
open scoped BigOperators

namespace AdderTrace

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Columns are the images of computational-basis vectors. -/
def permutationMatrix (p : Equiv.Perm β) : Matrix β β ℂ :=
  fun i j => if i = p j then 1 else 0

omit [Fintype β] in
@[simp] theorem permutationMatrix_one :
    permutationMatrix (1 : Equiv.Perm β) = 1 := by
  ext i j
  simp [permutationMatrix, Matrix.one_apply]

@[simp] theorem permutationMatrix_mul (p q : Equiv.Perm β) :
    permutationMatrix (p * q) = permutationMatrix p * permutationMatrix q := by
  ext i j
  simp [permutationMatrix, Matrix.mul_apply, mul_ite]

/-- The action on basis labels is represented by a multiplicative matrix map. -/
def permutationMatrixHom : Equiv.Perm β →* Matrix β β ℂ where
  toFun := permutationMatrix
  map_one' := permutationMatrix_one
  map_mul' := permutationMatrix_mul

/-- A permutation matrix's trace counts exactly its fixed basis labels. -/
theorem trace_permutationMatrix (p : Equiv.Perm β) :
    Matrix.trace (permutationMatrix p) =
      (Fintype.card {x : β // p x = x} : ℂ) := by
  classical
  simp [Matrix.trace, Matrix.diag, permutationMatrix, eq_comm,
    Fintype.card_subtype, Finset.sum_boole]

/-- An ordered product of permutation matrices represents the ordered
product of the underlying permutations. -/
theorem permutationMatrix_list_prod (ps : List (Equiv.Perm β)) :
    (ps.map permutationMatrix).prod = permutationMatrix ps.prod := by
  exact (map_list_prod permutationMatrixHom ps).symm

/-- The trace/fixed-label identity applies to any operator word. -/
theorem trace_permutation_word {m : ℕ} (word : Fin m → Equiv.Perm β) :
    Matrix.trace (List.ofFn fun j => permutationMatrix (word j)).prod =
      (Fintype.card {x : β // (List.ofFn word).prod x = x} : ℂ) := by
  rw [List.ofFn_comp', permutationMatrix_list_prod, trace_permutationMatrix]

end AdderTrace


/-! Source component: TensorFixedLabels.lean -/

open scoped BigOperators

namespace AdderTrace

noncomputable section

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Proportion of computational labels fixed by a permutation. -/
def fixedRatio (p : Equiv.Perm β) : ℝ :=
  (Fintype.card {x : β // p x = x} : ℝ) / Fintype.card β

lemma fixedRatio_nonneg (p : Equiv.Perm β) : 0 ≤ fixedRatio p :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma fixedRatio_le_one (p : Equiv.Perm β) : fixedRatio p ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast Fintype.card_subtype_le (fun x => p x = x))
    (Nat.cast_nonneg _)

/-- Normalized real matrix trace is exactly the fraction of fixed labels. -/
lemma normalized_permutation_trace_re (p : Equiv.Perm β) :
    (Matrix.trace (permutationMatrix p) / (Fintype.card β : ℂ)).re =
      fixedRatio p := by
  rw [trace_permutationMatrix]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {δ : ι → Type*}
  [∀ i, Fintype (δ i)] [∀ i, DecidableEq (δ i)]

/-- Independent coordinate permutations on the Cartesian product of labels. -/
def coordinatePermutation (p : ∀ i, Equiv.Perm (δ i)) :
    Equiv.Perm (∀ i, δ i) := Equiv.piCongrRight p

/-- A product label is fixed precisely when each coordinate is fixed. -/
def coordinateFixedEquiv (p : ∀ i, Equiv.Perm (δ i)) :
    {x : (∀ i, δ i) // coordinatePermutation p x = x} ≃
      (∀ i, {x : δ i // p i x = x}) where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun x := ⟨fun i => (x i).val, funext (fun i => (x i).property)⟩
  left_inv x := by rfl
  right_inv x := by rfl

lemma coordinate_fixed_card (p : ∀ i, Equiv.Perm (δ i)) :
    Fintype.card {x : (∀ i, δ i) // coordinatePermutation p x = x} =
      ∏ i, Fintype.card {x : δ i // p i x = x} := by
  rw [Fintype.card_congr (coordinateFixedEquiv p), Fintype.card_pi]

lemma coordinate_fixedRatio (p : ∀ i, Equiv.Perm (δ i)) :
    fixedRatio (coordinatePermutation p) = ∏ i, fixedRatio (p i) := by
  classical
  simp only [fixedRatio, coordinate_fixed_card, Fintype.card_pi, Nat.cast_prod,
    Finset.prod_div_distrib]

/-- If one coordinate has few fixed labels, the full tensor permutation
has at most the same proportion of fixed labels. -/
theorem coordinate_fixedRatio_le (p : ∀ i, Equiv.Perm (δ i))
    (i₀ : ι) (ε : ℝ) (h : fixedRatio (p i₀) ≤ ε) :
    fixedRatio (coordinatePermutation p) ≤ ε := by
  classical
  rw [coordinate_fixedRatio]
  calc
    _ = (∏ i ∈ Finset.univ.erase i₀, fixedRatio (p i)) * fixedRatio (p i₀) :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i₀)).symm
    _ ≤ 1 * ε := mul_le_mul
      (Finset.prod_le_one (fun i _ => fixedRatio_nonneg (p i))
        (fun i _ => fixedRatio_le_one (p i))) h
      (fixedRatio_nonneg _) (by norm_num)
    _ = ε := one_mul _

/-- The finite-dimensional tensor trace bound, stated directly for matrices. -/
theorem coordinate_permutation_trace_re_le (p : ∀ i, Equiv.Perm (δ i))
    (i₀ : ι) (ε : ℝ) (h : fixedRatio (p i₀) ≤ ε) :
    (Matrix.trace (permutationMatrix (coordinatePermutation p)) /
      (Fintype.card (∀ i, δ i) : ℂ)).re ≤ ε := by
  rw [normalized_permutation_trace_re]
  exact coordinate_fixedRatio_le p i₀ ε h

end

end AdderTrace


/-! Source component: MomentTransfer.lean -/

/-!
# Finite-word moment comparison

These lemmas verify the finite-sum part of the trace comparison.  In the
application, `finiteTrace` is the normalized trace of a permutation word and
`freeTrace` is its identity coefficient.  The required wordwise discrepancy
is an explicit hypothesis; this file does not assume a bound on the final
moment and does not claim to construct the adder permutations.
-/

open scoped BigOperators

namespace AdderTrace

noncomputable section

variable {α : Type*} [Fintype α]

/-- Triangle inequality for a finite expansion whose wordwise discrepancies
are bounded by `ε`. -/
theorem weighted_trace_difference_le
    (coeff finiteTrace freeTrace : α → ℂ) (ε : ℝ)
    (hword : ∀ a, ‖finiteTrace a - freeTrace a‖ ≤ ε) :
    ‖(∑ a, coeff a * finiteTrace a) -
      ∑ a, coeff a * freeTrace a‖ ≤
      ε * ∑ a, ‖coeff a‖ := by
  classical
  calc
    ‖(∑ a, coeff a * finiteTrace a) - ∑ a, coeff a * freeTrace a‖ =
        ‖∑ a, coeff a * (finiteTrace a - freeTrace a)‖ := by
          congr 1
          simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ a, ‖coeff a * (finiteTrace a - freeTrace a)‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖coeff a‖ * ε := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hword a) (norm_nonneg _)
    _ = ε * ∑ a, ‖coeff a‖ := by rw [← Finset.sum_mul, mul_comm]

/-- Identity words have matching traces; all other words have zero free
trace and finite trace between `0` and `ε`. -/
theorem weighted_identity_trace_difference_le
    (coeff : α → ℂ) (finiteTrace freeTrace : α → ℝ)
    (identityWord : α → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (hidentity : ∀ a, identityWord a → finiteTrace a = freeTrace a)
    (hnonidentity : ∀ a, ¬ identityWord a →
      freeTrace a = 0 ∧ 0 ≤ finiteTrace a ∧ finiteTrace a ≤ ε) :
    ‖(∑ a, coeff a * (finiteTrace a : ℂ)) -
      ∑ a, coeff a * (freeTrace a : ℂ)‖ ≤
      ε * ∑ a, ‖coeff a‖ := by
  apply weighted_trace_difference_le
  intro a
  by_cases h : identityWord a
  · simp only [hidentity a h, sub_self, norm_zero]
    exact hε
  · obtain ⟨hz, hpos, hbound⟩ := hnonidentity a h
    simpa only [hz, Complex.ofReal_zero, sub_zero, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hpos] using hbound

/-- The sum of absolute values of all length-`m` coefficient products is
exactly the `m`th power of the sum of absolute values. -/
theorem word_coefficient_norm_sum (coeff : α → ℂ) (m : ℕ) :
    (∑ word : Fin m → α, ‖∏ j, coeff (word j)‖) =
      (∑ a, ‖coeff a‖) ^ m := by
  classical
  simp only [norm_prod]
  exact (Fintype.sum_pow (fun a => ‖coeff a‖) m).symm

/-- The explicit moment comparison, valid for any wordwise trace bound. -/
theorem word_moment_difference_le
    (coeff : α → ℂ) (m : ℕ)
    (finiteTrace freeTrace : (Fin m → α) → ℂ)
    (ε : ℝ)
    (hword : ∀ word, ‖finiteTrace word - freeTrace word‖ ≤ ε) :
    ‖(∑ word : Fin m → α, (∏ j, coeff (word j)) * finiteTrace word) -
      ∑ word : Fin m → α, (∏ j, coeff (word j)) * freeTrace word‖ ≤
      ε * (∑ a, ‖coeff a‖) ^ m := by
  have h := weighted_trace_difference_le
    (fun word : Fin m → α => ∏ j, coeff (word j))
    finiteTrace freeTrace ε hword
  rwa [word_coefficient_norm_sum] at h

/-- A real-valued version, specialized to the even moments used in the filter. -/
theorem even_moment_comparison
    (coeff : α → ℂ) (L : ℕ)
    (finiteTrace freeTrace : (Fin (2 * L) → α) → ℝ)
    (identityWord : (Fin (2 * L) → α) → Prop)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hidentity : ∀ word, identityWord word → finiteTrace word = freeTrace word)
    (hnonidentity : ∀ word, ¬ identityWord word →
      freeTrace word = 0 ∧ 0 ≤ finiteTrace word ∧ finiteTrace word ≤ ε) :
    ‖(∑ word : Fin (2 * L) → α,
        (∏ j, coeff (word j)) * (finiteTrace word : ℂ)) -
      ∑ word : Fin (2 * L) → α,
        (∏ j, coeff (word j)) * (freeTrace word : ℂ)‖ ≤
      ε * (∑ a, ‖coeff a‖) ^ (2 * L) := by
  have h := weighted_identity_trace_difference_le
    (fun word : Fin (2 * L) → α => ∏ j, coeff (word j))
    finiteTrace freeTrace identityWord ε hε hidentity hnonidentity
  rwa [word_coefficient_norm_sum] at h

/-- The coefficient bound used to pass from an entrywise `ℓ¹` norm to
a Hilbert--Schmidt norm. -/
theorem coefficient_l1_le_sqrt_card_l2 (coeff : α → ℂ) :
    (∑ a, ‖coeff a‖) ≤ Real.sqrt (Fintype.card α) *
      Real.sqrt (∑ a, ‖coeff a‖ ^ 2) := by
  simpa using (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun _ : α => (1 : ℝ)) (fun a => ‖coeff a‖))

/-- Ordered products retain the order of factors in a noncommutative algebra. -/
def wordOperator {R : Type*} [Monoid R] (op : α → R) {m : ℕ}
    (word : Fin m → α) : R :=
  (List.ofFn fun j => op (word j)).prod

omit [Fintype α] in
@[simp] theorem wordOperator_zero {R : Type*} [Monoid R]
    (op : α → R) (word : Fin 0 → α) : wordOperator op word = 1 := by
  simp [wordOperator]

omit [Fintype α] in
@[simp] theorem wordOperator_cons {R : Type*} [Monoid R]
    (op : α → R) {m : ℕ} (a : α) (word : Fin m → α) :
    wordOperator op (Fin.cons a word) = op a * wordOperator op word := by
  simp [wordOperator, List.ofFn_succ]

/-- Full noncommutative expansion of a power, with factors in their original order. -/
theorem sum_wordOperator {R : Type*} [Semiring R] (op : α → R) (m : ℕ) :
    (∑ word : Fin m → α, wordOperator op word) = (∑ a, op a) ^ m := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => α).sum_comp
      (fun word => wordOperator op word)]
    simp only [Fintype.sum_prod_type]
    change (∑ a, ∑ word : Fin m → α, wordOperator op (Fin.cons a word)) = _
    simp only [wordOperator_cons]
    simp_rw [← Finset.mul_sum, ih]
    rw [← Finset.sum_mul, pow_succ']

omit [Fintype α] in
/-- Scalar coefficients factor out of an ordered operator word. -/
theorem wordOperator_smul {R : Type*} [Semiring R] [Algebra ℂ R]
    (coeff : α → ℂ) (op : α → R) {m : ℕ} (word : Fin m → α) :
    wordOperator (fun a => coeff a • op a) word =
      (∏ j, coeff (word j)) • wordOperator op word := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Fin.cons_self_tail word]
    simp only [wordOperator_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ih]
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    rw [mul_comm]

/-- Applying a linear trace functional to a power gives the finite-word expansion. -/
theorem trace_moment_expansion {R : Type*} [Semiring R] [Algebra ℂ R]
    (coeff : α → ℂ) (op : α → R) (trace : R →ₗ[ℂ] ℂ) (m : ℕ) :
    trace ((∑ a, coeff a • op a) ^ m) =
      ∑ word : Fin m → α, (∏ j, coeff (word j)) * trace (wordOperator op word) := by
  rw [← sum_wordOperator]
  simp only [map_sum, wordOperator_smul, map_smul, smul_eq_mul]

/-- Wordwise trace control implies control of actual noncommutative moments.
No formula for the matrix-power expansion is taken as a hypothesis. -/
theorem algebra_moment_difference_le
    {R S : Type*} [Semiring R] [Algebra ℂ R] [Semiring S] [Algebra ℂ S]
    (coeff : α → ℂ) (finiteOp : α → R) (freeOp : α → S)
    (finiteTrace : R →ₗ[ℂ] ℂ) (freeTrace : S →ₗ[ℂ] ℂ)
    (m : ℕ) (ε : ℝ)
    (hword : ∀ word : Fin m → α,
      ‖finiteTrace (wordOperator finiteOp word) -
        freeTrace (wordOperator freeOp word)‖ ≤ ε) :
    ‖finiteTrace ((∑ a, coeff a • finiteOp a) ^ m) -
      freeTrace ((∑ a, coeff a • freeOp a) ^ m)‖ ≤
      ε * (∑ a, ‖coeff a‖) ^ m := by
  rw [trace_moment_expansion, trace_moment_expansion]
  exact word_moment_difference_le coeff m _ _ ε hword

/-- Normalized matrix trace as a linear functional. -/
def normalizedMatrixTrace (β : Type*) [Fintype β] :
    Matrix β β ℂ →ₗ[ℂ] ℂ :=
  (Fintype.card β : ℂ)⁻¹ • Matrix.traceLinearMap β ℂ ℂ

@[simp] theorem normalizedMatrixTrace_apply {β : Type*} [Fintype β]
    (X : Matrix β β ℂ) :
    normalizedMatrixTrace β X = Matrix.trace X / (Fintype.card β : ℂ) := by
  simp [normalizedMatrixTrace, div_eq_mul_inv, mul_comm]

/-- Concrete normalized matrix traces satisfy the same comparison.
The reference algebra can, for example, be the algebra of bounded operators
in the left regular representation of a free group. -/
theorem matrix_moment_difference_le
    {β S : Type*} [Fintype β] [DecidableEq β] [Semiring S] [Algebra ℂ S]
    (coeff : α → ℂ) (finiteOp : α → Matrix β β ℂ) (freeOp : α → S)
    (freeTrace : S →ₗ[ℂ] ℂ) (m : ℕ) (ε : ℝ)
    (hword : ∀ word : Fin m → α,
      ‖Matrix.trace (wordOperator finiteOp word) / (Fintype.card β : ℂ) -
        freeTrace (wordOperator freeOp word)‖ ≤ ε) :
    ‖Matrix.trace ((∑ a, coeff a • finiteOp a) ^ m) / (Fintype.card β : ℂ) -
      freeTrace ((∑ a, coeff a • freeOp a) ^ m)‖ ≤
      ε * (∑ a, ‖coeff a‖) ^ m := by
  simpa only [normalizedMatrixTrace_apply] using
    algebra_moment_difference_le coeff finiteOp freeOp
      (normalizedMatrixTrace β) freeTrace m ε
      (fun word => by simpa only [normalizedMatrixTrace_apply] using hword word)

/-- The real upper-bound form of the moment comparison, used when the
reference even moment has already been bounded. -/
theorem matrix_moment_re_le
    {β S : Type*} [Fintype β] [DecidableEq β] [Semiring S] [Algebra ℂ S]
    (coeff : α → ℂ) (finiteOp : α → Matrix β β ℂ) (freeOp : α → S)
    (freeTrace : S →ₗ[ℂ] ℂ) (m : ℕ) (ε K : ℝ)
    (hword : ∀ word : Fin m → α,
      ‖Matrix.trace (wordOperator finiteOp word) / (Fintype.card β : ℂ) -
        freeTrace (wordOperator freeOp word)‖ ≤ ε)
    (hreference : (freeTrace ((∑ a, coeff a • freeOp a) ^ m)).re ≤ K) :
    (Matrix.trace ((∑ a, coeff a • finiteOp a) ^ m) /
      (Fintype.card β : ℂ)).re ≤ K + ε * (∑ a, ‖coeff a‖) ^ m := by
  have h := matrix_moment_difference_le coeff finiteOp freeOp freeTrace m ε hword
  have hre := (Complex.re_le_norm _).trans h
  simp only [Complex.sub_re] at hre
  calc
    _ ≤ ε * (∑ a, ‖coeff a‖) ^ m +
        (freeTrace ((∑ a, coeff a • freeOp a) ^ m)).re :=
      (sub_le_iff_le_add).mp hre
    _ ≤ K + ε * (∑ a, ‖coeff a‖) ^ m := by
      rw [add_comm]
      exact add_le_add_right hreference _

end

end AdderTrace


/-! Source component: ConcreteAdders.lean -/

open scoped BigOperators

namespace AdderTrace

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev AdderIndex (r M : ℕ) := Fin r → Fin M
abbrev TensorLabel (Q r : ℕ) := Fin r → (ZMod Q × ZMod Q)
abbrev AdderFreeGroup (r M : ℕ) := Fin r → FreeGroup (Fin M)

/-- A tuple of free generators, with the same index as the tensor adder. -/
def tupleGenerator {r M : ℕ} (I : AdderIndex r M) : AdderFreeGroup r M :=
  fun s => FreeGroup.of (I s)

/-- Exact free reference for U_I^* U_J. -/
def pairFree {r M : ℕ} (p : AdderIndex r M × AdderIndex r M) : AdderFreeGroup r M :=
  (tupleGenerator p.1)⁻¹ * tupleGenerator p.2

/-- The concrete tensor representation of the direct product of free groups. -/
def tensorRepresentation (Q r M : ℕ) : AdderFreeGroup r M →* Equiv.Perm (TensorLabel Q r) where
  toFun g := coordinatePermutation fun s =>
    modularRepresentation Q (FreeGroup.map Fin.val (g s))
  map_one' := by
    apply Equiv.ext
    intro x
    funext s
    change modularRepresentation Q (FreeGroup.map Fin.val (1 : FreeGroup (Fin M))) (x s) = x s
    simp
  map_mul' g h := by
    apply Equiv.ext
    intro x
    funext s
    change modularRepresentation Q (FreeGroup.map Fin.val (g s * h s)) (x s) =
      modularRepresentation Q (FreeGroup.map Fin.val (g s))
        (modularRepresentation Q (FreeGroup.map Fin.val (h s)) (x s))
    simp

/-- This is the actual coordinate permutation T_i1 tensor ... tensor T_ir. -/
def tensorAdder (Q : ℕ) {r M : ℕ} (I : AdderIndex r M) : Equiv.Perm (TensorLabel Q r) :=
  tensorRepresentation Q r M (tupleGenerator I)

/-- The corresponding permutation unitary, with columns labelled by inputs. -/
def tensorAdderMatrix (Q : ℕ) [NeZero Q] {r M : ℕ} (I : AdderIndex r M) :
    Matrix (TensorLabel Q r) (TensorLabel Q r) ℂ := permutationMatrix (tensorAdder Q I)

lemma tensorRepresentation_pair (Q : ℕ) {r M : ℕ}
    (p : AdderIndex r M × AdderIndex r M) :
    tensorRepresentation Q r M (pairFree p) = (tensorAdder Q p.1)⁻¹ * tensorAdder Q p.2 := by
  simp [pairFree, tensorAdder]

/-- Matrix adjoint agrees with inverse permutation. -/
lemma permutationMatrix_conjTranspose {β : Type*} [Fintype β] [DecidableEq β]
    (p : Equiv.Perm β) :
    (permutationMatrix p).conjTranspose = permutationMatrix p⁻¹ := by
  ext i j
  change star (if j = p i then (1 : ℂ) else 0) = if i = p.symm j then 1 else 0
  simp [Equiv.eq_symm_apply, eq_comm]

lemma tensorAdderMatrix_pair (Q : ℕ) [NeZero Q] {r M : ℕ}
    (p : AdderIndex r M × AdderIndex r M) :
    (tensorAdderMatrix Q p.1).conjTranspose * tensorAdderMatrix Q p.2 =
      permutationMatrix (tensorRepresentation Q r M (pairFree p)) := by
  rw [tensorRepresentation_pair]
  simp only [tensorAdderMatrix, permutationMatrix_conjTranspose, permutationMatrix_mul]

/-- The abstract product of a list of coefficient indices. -/
def pairFreeWord {r M : ℕ} (w : List (AdderIndex r M × AdderIndex r M)) :
    AdderFreeGroup r M := (w.map pairFree).prod

/-- Its s-th coordinate written in the integer syllable notation. -/
def coordinatePairWord {r M : ℕ} (s : Fin r)
    (w : List (AdderIndex r M × AdderIndex r M)) : List AdderCones.Syllable :=
  w.flatMap fun p => [((p.1 s).val, -1), ((p.2 s).val, 1)]

lemma coordinatePairWord_length {r M : ℕ} (s : Fin r)
    (w : List (AdderIndex r M × AdderIndex r M)) :
    (coordinatePairWord s w).length = 2*w.length := by
  induction w with
  | nil => simp [coordinatePairWord]
  | cons p w ih => simp [coordinatePairWord, List.flatMap_cons] at *; omega

lemma coordinatePairWord_letters {r M : ℕ} (s : Fin r)
    (w : List (AdderIndex r M × AdderIndex r M)) :
    ∀ p ∈ coordinatePairWord s w, |p.2| = 1 ∧ p.1 < M := by
  intro p hp
  obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨by norm_num, (q.1 s).isLt⟩
  · exact ⟨by norm_num, (q.2 s).isLt⟩

lemma coordinatePairWord_free {r M : ℕ} (s : Fin r)
    (w : List (AdderIndex r M × AdderIndex r M)) :
    AdderCones.freeWord (coordinatePairWord s w) =
      FreeGroup.map Fin.val (pairFreeWord w s) := by
  induction w with
  | nil => simp [coordinatePairWord, AdderCones.freeWord, pairFreeWord]
  | cons p w ih =>
    change AdderCones.freeWord
      ([((p.1 s).val,-1),((p.2 s).val,1)] ++ coordinatePairWord s w) = _
    have hprod : pairFreeWord (p::w) s = pairFree p s * pairFreeWord w s := rfl
    rw [hprod]
    simp only [AdderCones.freeWord, List.map_append, List.prod_append] at ih ⊢
    rw [ih]
    simp [pairFree, tupleGenerator]

lemma freeGroup_map_fin_injective (M : ℕ) (hM : 0 < M) :
    Function.Injective (FreeGroup.map (Fin.val : Fin M → ℕ)) := by
  let f : ℕ → Fin M := fun i => if h : i < M then ⟨i,h⟩ else ⟨0,hM⟩
  have hf (i : Fin M) : f i.val = i := by simp [f, i.isLt]
  have hl : Function.LeftInverse (FreeGroup.map f) (FreeGroup.map Fin.val) := by
    intro g
    rw [FreeGroup.map.comp]
    have hfi : f ∘ (Fin.val : Fin M → ℕ) = id := funext hf
    rw [hfi, FreeGroup.map.id]
  exact hl.injective

/-- The tensor permutation associated with a word has the desired trace
bound whenever its free-group reference is nonidentity. -/
theorem tensor_word_fixedRatio_le (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (w : List (AdderIndex r M × AdderIndex r M))
    (hlen : w.length = 2*L) (hne : pairFreeWord w ≠ 1) :
    fixedRatio (tensorRepresentation Q r M (pairFreeWord w)) ≤
      ((4*M-1)^(4*L)+1 : ℕ)/(Q:ℝ) := by
  classical
  have hex : ∃ s : Fin r, pairFreeWord w s ≠ 1 := by
    by_contra! h
    apply hne
    funext s
    exact h s
  obtain ⟨s, hs⟩ := hex
  change fixedRatio (coordinatePermutation fun s =>
    modularRepresentation Q (FreeGroup.map Fin.val (pairFreeWord w s))) ≤ _
  apply coordinate_fixedRatio_le _ s
  have hfree : AdderCones.freeWord (coordinatePairWord s w) ≠ 1 := by
    rw [coordinatePairWord_free]
    intro h
    apply hs
    apply freeGroup_map_fin_injective M (by omega)
    simpa using h
  have hlen' : (coordinatePairWord s w).length = 4*L := by
    rw [coordinatePairWord_length, hlen]
    omega
  have h := modular_word_fixedRatio_le Q M L hM (coordinatePairWord s w)
    hfree hlen' (coordinatePairWord_letters s w)
  rw [coordinatePairWord_free] at h
  simpa only [fixedRatio, Fintype.card_prod, ZMod.card, Nat.cast_mul, pow_two] using h


lemma tensorLabel_card (Q r : ℕ) [NeZero Q] :
    Fintype.card (TensorLabel Q r) = Q^(2*r) := by
  simp [TensorLabel, Fintype.card_fun, Fintype.card_prod, ZMod.card, pow_mul, pow_two]

lemma fixedRatio_one {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β] :
    fixedRatio (1 : Equiv.Perm β) = 1 := by
  simp [fixedRatio, Fintype.card_ne_zero]

lemma normalized_permutation_trace {β : Type*} [Fintype β] [DecidableEq β]
    (p : Equiv.Perm β) :
    Matrix.trace (permutationMatrix p)/(Fintype.card β : ℂ) = (fixedRatio p : ℂ) := by
  rw [trace_permutationMatrix]
  simp only [fixedRatio, Complex.ofReal_div, Complex.ofReal_natCast]

lemma tensor_pair_matrix_list (Q : ℕ) [NeZero Q] {r M : ℕ}
    (w : List (AdderIndex r M × AdderIndex r M)) :
    (w.map fun p => (tensorAdderMatrix Q p.1).conjTranspose * tensorAdderMatrix Q p.2).prod =
      permutationMatrix (tensorRepresentation Q r M (pairFreeWord w)) := by
  induction w with
  | nil => simp [pairFreeWord]
  | cons p w ih =>
    change ((tensorAdderMatrix Q p.1).conjTranspose * tensorAdderMatrix Q p.2) *
      (w.map fun p => (tensorAdderMatrix Q p.1).conjTranspose * tensorAdderMatrix Q p.2).prod =
      permutationMatrix (tensorRepresentation Q r M (pairFree p * pairFreeWord w))
    rw [map_mul, permutationMatrix_mul, tensorAdderMatrix_pair, ih]

lemma tensor_pair_matrix_word (Q : ℕ) [NeZero Q] {r M m : ℕ}
    (w : Fin m → AdderIndex r M × AdderIndex r M) :
    wordOperator (fun p => (tensorAdderMatrix Q p.1).conjTranspose * tensorAdderMatrix Q p.2) w =
      permutationMatrix (tensorRepresentation Q r M (pairFreeWord (List.ofFn w))) := by
  unfold wordOperator
  rw [List.ofFn_comp' w (fun p => (tensorAdderMatrix Q p.1).conjTranspose * tensorAdderMatrix Q p.2)]
  exact tensor_pair_matrix_list Q (List.ofFn w)

/-- The actual matrix word has normalized trace 1 when the free reference
is the identity and at most B_L/Q otherwise. -/
theorem concrete_word_trace_discrepancy (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (w : Fin (2*L) → AdderIndex r M × AdderIndex r M) :
    ‖Matrix.trace
      (wordOperator (fun p => (tensorAdderMatrix Q p.1).conjTranspose * tensorAdderMatrix Q p.2) w)
      / (Q^(2*r) : ℕ) -
      (if pairFreeWord (List.ofFn w) = 1 then (1:ℂ) else 0)‖ ≤
      ((4*M-1)^(4*L)+1 : ℕ)/(Q:ℝ) := by
  classical
  rw [tensor_pair_matrix_word, ← tensorLabel_card Q r, normalized_permutation_trace]
  by_cases h : pairFreeWord (List.ofFn w) = 1
  · rw [h, map_one, fixedRatio_one]
    simp only [Complex.ofReal_one, ↓reduceIte, sub_self, norm_zero]
    positivity
  · rw [if_neg h, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fixedRatio_nonneg _)]
    exact tensor_word_fixedRatio_le Q r M L hM (List.ofFn w) (by simp) h

/-- The same estimate with the free product written using `wordOperator`,
matching the coefficient expansion of an even matrix moment. -/
theorem concrete_word_trace_discrepancy' (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (w : Fin (2*L) → AdderIndex r M × AdderIndex r M) :
    ‖normalizedMatrixTrace (TensorLabel Q r)
      (wordOperator (fun p => (tensorAdderMatrix Q p.1).conjTranspose * tensorAdderMatrix Q p.2) w) -
      (if wordOperator pairFree w = 1 then (1:ℂ) else 0)‖ ≤
      ((4*M-1)^(4*L)+1 : ℕ)/(Q:ℝ) := by
  have h := concrete_word_trace_discrepancy Q r M L hM w
  simpa only [normalizedMatrixTrace_apply, tensorLabel_card,
    wordOperator, List.ofFn_comp', pairFreeWord] using h

#print axioms concrete_word_trace_discrepancy

end
end AdderTrace


/-! Source component: FinalBounds.lean -/

/-!
Final finite-sum and normalization steps of the trace estimate.
The hypotheses called `hmoment`, `hpoint`, and `hcard` below are explicit
interfaces; this module does not prove the free-group operator estimate or
identify the cardinality of the original Hermitian grid.
-/

open scoped BigOperators

namespace AdderTrace

noncomputable def delta (M r : ℕ) : ℝ :=
  Real.sqrt (((M : ℝ) + 9) ^ r - (M : ℝ) ^ r)

def wordBound (M L : ℕ) : ℕ := (4 * M - 1) ^ (4 * L) + 1

noncomputable def traceRHS (C₁ C₂ : ℝ) (M r L Q : ℕ) : ℝ :=
  let k := M ^ r
  ((2 * Nat.ceil (Real.sqrt C₁ * k)) ^ (k * (k - 1)) : ℕ) *
    ((Real.sqrt C₁ * delta M r / C₂) ^ (2 * L) +
      (wordBound M L : ℝ) / Q *
        (Real.sqrt (C₁ * k * (k - 1 : ℕ)) / C₂) ^ (2 * L))

theorem normalize_moment_bound
    (a x y D R K C ε : ℝ) (m : ℕ)
    (hD : 0 ≤ D) (hK : 0 < K) (hC : 0 < C)
    (hε : 0 ≤ ε) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ R * K) (hy : y ≤ x * Real.sqrt (K * (K - 1)))
    (hmoment : a ≤ (D * x) ^ m + ε * y ^ m) :
    a / (C * K) ^ m ≤
      (R * D / C) ^ m + ε * (R * Real.sqrt (K * (K - 1)) / C) ^ m := by
  have hCK : 0 < C * K := mul_pos hC hK
  have hpow : 0 < (C * K) ^ m := pow_pos hCK m
  have hx' : D * x / (C * K) ≤ R * D / C := by
    apply (div_le_iff₀ hCK).2
    calc
      D * x ≤ D * (R * K) := mul_le_mul_of_nonneg_left hx hD
      _ = R * D / C * (C * K) := by field_simp
  have hy' : y / (C * K) ≤ R * Real.sqrt (K * (K - 1)) / C := by
    apply (div_le_iff₀ hCK).2
    calc
      y ≤ x * Real.sqrt (K * (K - 1)) := hy
      _ ≤ (R * K) * Real.sqrt (K * (K - 1)) :=
        mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg _)
      _ = R * Real.sqrt (K * (K - 1)) / C * (C * K) := by field_simp
  calc
    a / (C * K) ^ m ≤ ((D * x) ^ m + ε * y ^ m) / (C * K) ^ m :=
      div_le_div_of_nonneg_right hmoment (le_of_lt hpow)
    _ = (D * x / (C * K)) ^ m + ε * (y / (C * K)) ^ m := by
      rw [add_div, div_pow, div_pow]
      ring
    _ ≤ (R * D / C) ^ m + ε * (R * Real.sqrt (K * (K - 1)) / C) ^ m := by
      apply add_le_add
      · exact pow_le_pow_left₀ (div_nonneg (mul_nonneg hD hx0) (le_of_lt hCK)) hx' m
      · exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg hy0 (le_of_lt hCK)) hy' m) hε

theorem finite_sum_bound
    {α : Type*} (S : Finset α) (f : α → ℝ) (N : ℕ) (b : ℝ)
    (hb : 0 ≤ b) (hcard : S.card ≤ N)
    (hpoint : ∀ x ∈ S, f x ≤ b) :
    (∑ x ∈ S, f x) ≤ (N : ℝ) * b := by
  calc
    (∑ x ∈ S, f x) ≤ ∑ _x ∈ S, b := Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * b := by simp
    _ ≤ (N : ℝ) * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hb

noncomputable def momentMatrix {K N : Type*}
    [Fintype K] [Fintype N] [DecidableEq K]
    (U : K → Matrix N N ℂ) (W : Matrix K K ℂ) : Matrix N N ℂ :=
  ∑ i, ∑ j, if i = j then 0 else W i j • ((U i).conjTranspose * U j)

noncomputable def filterMatrix {K N : Type*}
    [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]
    (S : Finset (Matrix K K ℂ)) (U : K → Matrix N N ℂ) (c : ℝ) (L : ℕ) :
    Matrix N N ℂ :=
  ∑ W ∈ S, (((c⁻¹ : ℝ) : ℂ) • momentMatrix U W) ^ (2 * L)

noncomputable def normalizedTrace {N : Type*} [Fintype N]
    (A : Matrix N N ℂ) : ℝ := (Matrix.trace A).re / Fintype.card N

theorem normalizedTrace_sum {α N : Type*} [Fintype N]
    (S : Finset α) (f : α → Matrix N N ℂ) :
    normalizedTrace (∑ x ∈ S, f x) = ∑ x ∈ S, normalizedTrace (f x) := by
  simp [normalizedTrace, Matrix.trace_sum, Complex.re_sum, div_eq_mul_inv, Finset.sum_mul]

/-- A conditional assembly theorem. Its pointwise moment estimate and grid
cardinality bound are hypotheses, not axioms and not silently discharged. -/
theorem filter_bound_of_pointwise_and_card
    {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]
    (S : Finset (Matrix K K ℂ)) (U : K → Matrix N N ℂ)
    (c b : ℝ) (L count : ℕ)
    (hb : 0 ≤ b) (hcard : S.card ≤ count)
    (hpoint : ∀ W ∈ S,
      normalizedTrace ((((c⁻¹ : ℝ) : ℂ) • momentMatrix U W) ^ (2 * L)) ≤ b) :
    normalizedTrace (filterMatrix S U c L) ≤ (count : ℝ) * b := by
  unfold filterMatrix
  rw [normalizedTrace_sum]
  exact finite_sum_bound S _ count b hb hcard hpoint

#print axioms normalize_moment_bound
#print axioms finite_sum_bound
#print axioms normalizedTrace_sum
#print axioms filter_bound_of_pointwise_and_card

end AdderTrace


/-! Source component: ConcreteMoments.lean -/

open scoped BigOperators

namespace AdderTrace
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The canonical identity coefficient of the complex group algebra. -/
def identityCoefficient (G : Type*) [Group G] : MonoidAlgebra ℂ G →ₗ[ℂ] ℂ where
  toFun f := f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma identityCoefficient_apply {G : Type*} [Group G]
    (f : MonoidAlgebra ℂ G) : identityCoefficient G f = f 1 := rfl

/-- The reference word in the group algebra is a single group-basis element. -/
lemma wordOperator_groupBasis {A G : Type*} [Monoid G]
    (op : A → G) {m : ℕ} (w : Fin m → A) :
    wordOperator (fun a => MonoidAlgebra.of ℂ G (op a)) w =
      MonoidAlgebra.of ℂ G (wordOperator op w) := by
  unfold wordOperator
  rw [List.ofFn_comp' w (fun a => MonoidAlgebra.of ℂ G (op a))]
  rw [List.ofFn_comp' w op]
  simpa only [List.map_map, Function.comp_apply] using
    (map_list_prod (MonoidAlgebra.of ℂ G) ((List.ofFn w).map op)).symm

lemma identityCoefficient_word {A G : Type*} [Group G]
    (op : A → G) {m : ℕ} (w : Fin m → A) :
    identityCoefficient G (wordOperator (fun a => MonoidAlgebra.of ℂ G (op a)) w) =
      if wordOperator op w = 1 then 1 else 0 := by
  classical
  rw [wordOperator_groupBasis]
  simp [MonoidAlgebra.of_apply, MonoidAlgebra.single_apply]

/-- Actual normalized finite-dimensional and group-algebra moments differ
by the explicit fixed-label error. No trace estimate is a premise. -/
theorem concrete_moment_difference (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (W : Matrix (AdderIndex r M) (AdderIndex r M) ℂ) :
    ‖normalizedMatrixTrace (TensorLabel Q r)
        ((∑ I, ∑ J, W I J •
          ((tensorAdderMatrix Q I).conjTranspose * tensorAdderMatrix Q J)) ^ (2 * L)) -
      (ExplicitFilter.freePolynomial W ^ (2 * L)) 1‖ ≤
      (((4 * M - 1) ^ (4 * L) + 1 : ℕ) : ℝ) / Q *
        (∑ I, ∑ J, ‖W I J‖) ^ (2 * L) := by
  classical
  have h := algebra_moment_difference_le
    (fun p : AdderIndex r M × AdderIndex r M => W p.1 p.2)
    (fun p => (tensorAdderMatrix Q p.1).conjTranspose * tensorAdderMatrix Q p.2)
    (fun p => MonoidAlgebra.of ℂ (AdderFreeGroup r M) (pairFree p))
    (normalizedMatrixTrace (TensorLabel Q r)) (identityCoefficient (AdderFreeGroup r M))
    (2 * L) ((((4 * M - 1) ^ (4 * L) + 1 : ℕ) : ℝ) / Q)
    (fun w => by
      rw [identityCoefficient_word]
      have hw := concrete_word_trace_discrepancy' Q r M L hM w
      by_cases hidentity : wordOperator pairFree w = 1
      · simpa only [if_pos hidentity] using hw
      · simpa only [if_neg hidentity] using hw)
  simpa only [Fintype.sum_prod_type, identityCoefficient_apply,
    MonoidAlgebra.of_apply, ExplicitFilter.freePolynomial,
    pairFree, tupleGenerator, ExplicitFilter.generatorTuple] using h

/-- For zero-diagonal coefficients the finite sum is exactly the prescribed A(W). -/
lemma momentMatrix_eq_full_sum (Q r M : ℕ) [NeZero Q]
    (W : Matrix (AdderIndex r M) (AdderIndex r M) ℂ) (hdiag : ∀ I, W I I = 0) :
    momentMatrix (tensorAdderMatrix Q) W =
      ∑ I, ∑ J, W I J •
        ((tensorAdderMatrix Q I).conjTranspose * tensorAdderMatrix Q J) := by
  classical
  unfold momentMatrix
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h : I = J
  · subst J
    simp [hdiag]
  · simp [h]

/-- Concrete matrix moment upper bound in terms of the actual free moment. -/
theorem concrete_moment_re_le (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (W : Matrix (AdderIndex r M) (AdderIndex r M) ℂ)
    (hdiag : ∀ I, W I I = 0) :
    normalizedTrace ((momentMatrix (tensorAdderMatrix Q) W) ^ (2 * L)) ≤
      ‖(ExplicitFilter.freePolynomial W ^ (2 * L)) 1‖ +
      (((4 * M - 1) ^ (4 * L) + 1 : ℕ) : ℝ) / Q *
        (∑ I, ∑ J, ‖W I J‖) ^ (2 * L) := by
  have h := concrete_moment_difference Q r M L hM W
  have hre := (Complex.re_le_norm _).trans h
  simp only [Complex.sub_re] at hre
  have hfree := Complex.re_le_norm ((ExplicitFilter.freePolynomial W ^ (2 * L)) 1)
  rw [momentMatrix_eq_full_sum Q r M W hdiag]
  have heq (A : Matrix (TensorLabel Q r) (TensorLabel Q r) ℂ) :
      normalizedTrace A = (normalizedMatrixTrace (TensorLabel Q r) A).re := by
    simp only [normalizedTrace, normalizedMatrixTrace_apply,
      ← Complex.ofReal_natCast, Complex.div_ofReal_re]
  rw [heq]
  linarith

end
end AdderTrace


/-! Source component: FreeMomentBounds.lean -/

open scoped BigOperators
open AdderTrace.PrefixOperators

namespace AdderTrace
noncomputable section

lemma delta_sq (M r : ℕ) : delta M r ^ 2 = ((M : ℝ) + 9) ^ r - (M : ℝ) ^ r := by
  unfold delta
  apply Real.sq_sqrt
  apply sub_nonneg.mpr
  exact pow_le_pow_left₀ (Nat.cast_nonneg M) (by linarith) r

lemma coefficient_energy_eq_trace_sq {K : Type*} [Fintype K] [DecidableEq K]
    (W : Matrix K K ℂ) (hW : W.IsHermitian) :
    (∑ I, ∑ J, ‖W I J‖ ^ 2) = (Matrix.trace (W ^ 2)).re := by
  simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← hW.apply J I]
  change ‖W I J‖ * ‖W I J‖ = (W I J * starRingEnd ℂ (W I J)).re
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_two]

/-- Converting the exact squared convolution constant to the stated
Delta times Hilbert--Schmidt radius. -/
theorem free_even_moment_of_delta_convolution (r M L : ℕ)
    (W : Matrix (AdderIndex r M) (AdderIndex r M) ℂ)
    (hconv : ∀ f : ExplicitFilter.TupleWord (Fin r) (Fin M) →₀ ℂ,
      (∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) →
      ExplicitFilter.l2Sq (ExplicitFilter.tupleConvolution W f) ≤
        (((M : ℝ) + 9) ^ r - (M : ℝ) ^ r) *
          (∑ I, ∑ J, ‖W I J‖ ^ 2) * ExplicitFilter.l2Sq f) :
    ‖(ExplicitFilter.freePolynomial W ^ (2 * L)) 1‖ ≤
      (delta M r * Real.sqrt (∑ I, ∑ J, ‖W I J‖ ^ 2)) ^ (2 * L) := by
  apply ExplicitFilter.freePolynomial_even_moment_bound
  intro f hf
  have h := hconv f hf
  rwa [mul_pow, delta_sq, Real.sq_sqrt (by positivity)]

/-- The complete raw moment estimate after supplying the actual full
convolution bound. This is the sole remaining analytic input. -/
theorem concrete_moment_of_delta_convolution (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (W : Matrix (AdderIndex r M) (AdderIndex r M) ℂ)
    (hdiag : ∀ I, W I I = 0)
    (hconv : ∀ f : ExplicitFilter.TupleWord (Fin r) (Fin M) →₀ ℂ,
      (∀ w ∈ f.support, ∀ t, FreeGroup.IsReduced (w t)) →
      ExplicitFilter.l2Sq (ExplicitFilter.tupleConvolution W f) ≤
        (((M : ℝ) + 9) ^ r - (M : ℝ) ^ r) *
          (∑ I, ∑ J, ‖W I J‖ ^ 2) * ExplicitFilter.l2Sq f) :
    normalizedTrace ((momentMatrix (tensorAdderMatrix Q) W) ^ (2 * L)) ≤
      (delta M r * Real.sqrt (∑ I, ∑ J, ‖W I J‖ ^ 2)) ^ (2 * L) +
      (wordBound M L : ℝ) / Q * (∑ I, ∑ J, ‖W I J‖) ^ (2 * L) := by
  exact (concrete_moment_re_le Q r M L hM W hdiag).trans
    (add_le_add_right (free_even_moment_of_delta_convolution r M L W hconv) _)

end
end AdderTrace


/-! Source component: VerifiedMomentBound.lean -/

open scoped BigOperators

namespace AdderTrace
noncomputable section

/-- The full free-polynomial even-moment estimate, with no analytic
estimate left as a hypothesis. -/
theorem free_polynomial_even_moment_bound (r M L : ℕ) (hM : 2 ≤ M)
    (W : Matrix (AdderIndex r M) (AdderIndex r M) ℂ)
    (hdiag : ∀ I, W I I = 0) :
    ‖(ExplicitFilter.freePolynomial W ^ (2 * L)) 1‖ ≤
      (delta M r * Real.sqrt (∑ I, ∑ J, ‖W I J‖ ^ 2)) ^ (2 * L) := by
  letI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  apply free_even_moment_of_delta_convolution
  intro f hf
  simpa only [Fintype.card_fin] using
    ExplicitFilter.full_tensor_convolution_bound W hdiag f hf

/-- The complete raw matrix-moment estimate for the explicitly prescribed
adder matrices. All free-group and finite-permutation bounds are proved. -/
theorem tensor_adder_moment_bound (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (W : Matrix (AdderIndex r M) (AdderIndex r M) ℂ)
    (hdiag : ∀ I, W I I = 0) :
    normalizedTrace ((momentMatrix (tensorAdderMatrix Q) W) ^ (2 * L)) ≤
      (delta M r * Real.sqrt (∑ I, ∑ J, ‖W I J‖ ^ 2)) ^ (2 * L) +
      (wordBound M L : ℝ) / Q * (∑ I, ∑ J, ‖W I J‖) ^ (2 * L) := by
  exact (concrete_moment_re_le Q r M L hM W hdiag).trans
    (add_le_add_right (free_polynomial_even_moment_bound r M L hM W hdiag) _)

/-- Hermitian coefficients express the same estimate in the user's
trace-of-square notation. -/
theorem tensor_adder_raw_moment_bound (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (W : Matrix (AdderIndex r M) (AdderIndex r M) ℂ)
    (hdiag : ∀ I, W I I = 0) (hH : ∀ I J, W J I = star (W I J)) :
    normalizedTrace ((momentMatrix (tensorAdderMatrix Q) W) ^ (2 * L)) ≤
      (delta M r * Real.sqrt ((Matrix.trace (W ^ 2)).re)) ^ (2 * L) +
      (wordBound M L : ℝ) / Q * (∑ I, ∑ J, ‖W I J‖) ^ (2 * L) := by
  have hh : W.IsHermitian := Matrix.IsHermitian.ext (fun I J => (hH J I).symm)
  have h := tensor_adder_moment_bound Q r M L hM W hdiag
  rwa [coefficient_energy_eq_trace_sq W hh] at h

#print axioms tensor_adder_raw_moment_bound

end
end AdderTrace


/-! Source component: MatrixGrid.lean -/

/-! Cardinality of the actual Gaussian-integer Hermitian matrix grid. -/

open scoped BigOperators

namespace AdderTrace.MatrixGrid

abbrev OffDiag (k : ℕ) := {p : Fin k × Fin k // p.1 ≠ p.2}

noncomputable def energy {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ) : ℝ :=
  ∑ p : Fin k × Fin k, Complex.normSq (W p.1 p.2)

noncomputable def code {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ)
    (p : OffDiag k) : ℤ :=
  if p.val.1 < p.val.2 then Int.floor (W p.val.1 p.val.2).re
  else Int.floor (W p.val.2 p.val.1).im

def IntegralEntries {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  ∀ i j, (∃ a : ℤ, (W i j).re = a) ∧ (∃ b : ℤ, (W i j).im = b)

theorem energy_eq_trace_sq {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ)
    (hH : ∀ i j, W j i = star (W i j)) :
    energy W = (Matrix.trace (W ^ 2)).re := by
  simp only [energy, Fintype.sum_prod_type, pow_two, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hH i j]
  change Complex.normSq (W i j) = (W i j * starRingEnd ℂ (W i j)).re
  simp [Complex.mul_conj]

theorem offDiag_card (k : ℕ) : Fintype.card (OffDiag k) = k * (k - 1) := by
  rw [Fintype.card_subtype]
  have heq : (Finset.univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2)) =
      (Finset.univ : Finset (Fin k)).offDiag := by
    ext p
    simp
  rw [heq, Finset.offDiag_card]
  simp [Nat.mul_sub_left_distrib]

theorem two_entry_le_energy {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ)
    (hH : ∀ i j, W j i = star (W i j)) (i j : Fin k) (hij : i ≠ j) :
    2 * Complex.normSq (W i j) ≤ energy W := by
  have hp : (i,j) ≠ (j,i) := by
    intro h
    exact hij (congrArg Prod.fst h)
  have hsub : ({(i,j), (j,i)} : Finset (Fin k × Fin k)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => Complex.normSq_nonneg (W p.1 p.2))
  simpa [energy, hp, Ne.symm hp, hH i j, Complex.normSq_conj, two_mul] using hh

theorem components_lt {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ)
    (hH : ∀ i j, W j i = star (W i j)) (R : ℝ) (hR : 0 < R)
    (he : energy W ≤ R ^ 2) (i j : Fin k) (hij : i ≠ j) :
    |(W i j).re| < R ∧ |(W i j).im| < R := by
  have htwo := (two_entry_le_energy W hH i j hij).trans he
  rw [Complex.normSq_apply] at htwo
  have hRe : (W i j).re ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (W i j).im]
  have hIm : (W i j).im ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (W i j).re]
  constructor
  · exact (sq_lt_sq₀ (abs_nonneg _) (le_of_lt hR)).mp (by simpa using hRe)
  · exact (sq_lt_sq₀ (abs_nonneg _) (le_of_lt hR)).mp (by simpa using hIm)

theorem code_injective_on {k : ℕ}
    (S : Finset (Matrix (Fin k) (Fin k) ℂ))
    (hD : ∀ W ∈ S, ∀ i, W i i = 0)
    (hH : ∀ W ∈ S, ∀ i j, W j i = star (W i j))
    (hInt : ∀ W ∈ S, IntegralEntries W) :
    Set.InjOn (@code k) (↑S : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  intro V hV W hW heq
  have hupper : ∀ i j : Fin k, i < j → V i j = W i j := by
    intro i j hij
    have hreal := congrFun heq (⟨(i,j), ne_of_lt hij⟩ : OffDiag k)
    have himag := congrFun heq (⟨(j,i), (ne_of_lt hij).symm⟩ : OffDiag k)
    simp only [code, hij, if_true] at hreal
    simp only [code, not_lt.mpr (le_of_lt hij), if_false] at himag
    obtain ⟨vr, hvr⟩ := (hInt V hV i j).1
    obtain ⟨wr, hwr⟩ := (hInt W hW i j).1
    obtain ⟨vi, hvi⟩ := (hInt V hV i j).2
    obtain ⟨wi, hwi⟩ := (hInt W hW i j).2
    rw [hvr, hwr, Int.floor_intCast, Int.floor_intCast] at hreal
    rw [hvi, hwi, Int.floor_intCast, Int.floor_intCast] at himag
    apply Complex.ext
    · simpa [hvr, hwr] using congrArg (fun z : ℤ => (z : ℝ)) hreal
    · simpa [hvi, hwi] using congrArg (fun z : ℤ => (z : ℝ)) himag
  funext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hupper i j hij
  · subst j
    rw [hD V hV i, hD W hW i]
  · rw [hH V hV j i, hH W hW j i, hupper j i hij]

theorem hermitian_grid_card_le {k : ℕ}
    (S : Finset (Matrix (Fin k) (Fin k) ℂ)) (R : ℝ) (hR : 0 < R)
    (hD : ∀ W ∈ S, ∀ i, W i i = 0)
    (hH : ∀ W ∈ S, ∀ i j, W j i = star (W i j))
    (hInt : ∀ W ∈ S, IntegralEntries W)
    (hE : ∀ W ∈ S, energy W ≤ R ^ 2) :
    S.card ≤ (2 * Nat.ceil R) ^ (k * (k - 1)) := by
  classical
  let c : ℤ := Nat.ceil R
  let B : Finset ℤ := Finset.Ico (-c) c
  have hc : R ≤ (c : ℝ) := by exact_mod_cast Nat.le_ceil R
  have hcoord : ∀ W ∈ S, ∀ p : OffDiag k, code W p ∈ B := by
    intro W hW p
    have hcomponent : ∃ z : ℤ, code W p = z ∧ |(z : ℝ)| < R := by
      by_cases hp : p.val.1 < p.val.2
      · obtain ⟨z, hz⟩ := (hInt W hW p.val.1 p.val.2).1
        refine ⟨z, ?_, ?_⟩
        · simp [code, hp, hz]
        · simpa [hz] using (components_lt W (hH W hW) R hR (hE W hW)
            p.val.1 p.val.2 p.property).1
      · obtain ⟨z, hz⟩ := (hInt W hW p.val.2 p.val.1).2
        refine ⟨z, ?_, ?_⟩
        · simp [code, hp, hz]
        · simpa [hz] using (components_lt W (hH W hW) R hR (hE W hW)
            p.val.2 p.val.1 p.property.symm).2
    obtain ⟨z, hz, hzr⟩ := hcomponent
    rw [hz]
    have hu : (z : ℝ) < (c : ℝ) := lt_of_lt_of_le (abs_lt.mp hzr).2 hc
    have hl : -(c : ℝ) < (z : ℝ) := by linarith [(abs_lt.mp hzr).1]
    apply Finset.mem_Ico.mpr
    constructor
    · have : -c < z := by exact_mod_cast hl
      exact le_of_lt this
    · exact_mod_cast hu
  have hsub : S.image code ⊆ Fintype.piFinset (fun _ : OffDiag k => B) := by
    intro x hx
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hx
    exact Fintype.mem_piFinset.mpr (hcoord W hW)
  have hcardB : B.card = 2 * Nat.ceil R := by
    simp only [B, Int.card_Ico]
    dsimp [c]
    omega
  calc
    S.card = (S.image code).card :=
      (Finset.card_image_of_injOn (code_injective_on S hD hH hInt)).symm
    _ ≤ (Fintype.piFinset (fun _ : OffDiag k => B)).card := Finset.card_le_card hsub
    _ = (2 * Nat.ceil R) ^ (k * (k - 1)) := by
      simp only [Fintype.card_piFinset, hcardB, Finset.prod_const,
        Finset.card_univ, offDiag_card]

theorem matrix_grid_card_le {k : ℕ}
    (S : Finset (Matrix (Fin k) (Fin k) ℂ)) (C₁ : ℝ)
    (hk : 0 < k) (hC₁ : 0 < C₁)
    (hD : ∀ W ∈ S, ∀ i, W i i = 0)
    (hH : ∀ W ∈ S, ∀ i j, W j i = star (W i j))
    (hInt : ∀ W ∈ S, IntegralEntries W)
    (hT : ∀ W ∈ S, (Matrix.trace (W ^ 2)).re ≤ C₁ * (k : ℝ) ^ 2) :
    S.card ≤ (2 * Nat.ceil (Real.sqrt C₁ * k)) ^ (k * (k - 1)) := by
  apply hermitian_grid_card_le S (Real.sqrt C₁ * k)
    (mul_pos (Real.sqrt_pos.2 hC₁) (by exact_mod_cast hk)) hD hH hInt
  intro W hW
  rw [energy_eq_trace_sq W (hH W hW), mul_pow, Real.sq_sqrt (le_of_lt hC₁)]
  exact hT W hW

#print axioms hermitian_grid_card_le
#print axioms matrix_grid_card_le
#print axioms energy_eq_trace_sq

end AdderTrace.MatrixGrid


/-! Source component: ReindexedAdders.lean -/

open scoped BigOperators

namespace AdderTrace

noncomputable section

lemma adderIndex_card (r M : ℕ) : Fintype.card (AdderIndex r M) = M^r := by
  simp [AdderIndex]

/-- Relabel the explicit tensor index set by Fin k, k=M^r. -/
def indexEquiv (r M : ℕ) : AdderIndex r M ≃ Fin (M^r) :=
  Fintype.equivFinOfCardEq (adderIndex_card r M)

/-- A coefficient matrix indexed by Fin k, read in tensor coordinates. -/
def liftedCoefficients {r M : ℕ} (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) :
    Matrix (AdderIndex r M) (AdderIndex r M) ℂ :=
  fun I J => W (indexEquiv r M I) (indexEquiv r M J)

/-- The explicit U_1,...,U_k matrices after a harmless relabeling of tuples. -/
def finAdderMatrix (Q r M : ℕ) [NeZero Q] (i : Fin (M^r)) :
    Matrix (TensorLabel Q r) (TensorLabel Q r) ℂ :=
  tensorAdderMatrix Q ((indexEquiv r M).symm i)

lemma liftedCoefficients_diagonal {r M : ℕ}
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) (hW : ∀ i, W i i = 0) :
    ∀ I, liftedCoefficients W I I = 0 := fun I => hW _

lemma liftedCoefficients_hermitian {r M : ℕ}
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ)
    (hW : ∀ i j, W j i = star (W i j)) :
    ∀ I J, liftedCoefficients W J I = star (liftedCoefficients W I J) :=
  fun I J => hW _ _

lemma liftedCoefficients_sum {r M : ℕ} {A : Type*} [AddCommMonoid A]
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) (f : ℂ → A) :
    (∑ p : AdderIndex r M × AdderIndex r M, f (liftedCoefficients W p.1 p.2)) =
      ∑ p : Fin (M^r) × Fin (M^r), f (W p.1 p.2) := by
  exact (Equiv.prodCongr (indexEquiv r M) (indexEquiv r M)).sum_comp
    (fun p => f (W p.1 p.2))

lemma liftedCoefficients_energy {r M : ℕ}
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) :
    (∑ I, ∑ J, ‖liftedCoefficients W I J‖^2) = MatrixGrid.energy W := by
  have h := liftedCoefficients_sum W (fun z => ‖z‖^2)
  simpa only [MatrixGrid.energy, Complex.normSq_eq_norm_sq, Fintype.sum_prod_type] using h

lemma liftedCoefficients_l1 {r M : ℕ}
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) :
    (∑ I, ∑ J, ‖liftedCoefficients W I J‖) =
      ∑ p : Fin (M^r) × Fin (M^r), ‖W p.1 p.2‖ := by
  simpa only [Fintype.sum_prod_type] using liftedCoefficients_sum W norm

/-- The matrix A(W) in tuple coordinates; diagonal coefficients may be zero. -/
def tupleTraceOperator (Q : ℕ) [NeZero Q] {r M : ℕ}
    (W : Matrix (AdderIndex r M) (AdderIndex r M) ℂ) :
    Matrix (TensorLabel Q r) (TensorLabel Q r) ℂ :=
  ∑ I, ∑ J, W I J • ((tensorAdderMatrix Q I).conjTranspose * tensorAdderMatrix Q J)

/-- The same A(W), now indexed by Fin k. -/
def finTraceOperator (Q r M : ℕ) [NeZero Q]
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) :
    Matrix (TensorLabel Q r) (TensorLabel Q r) ℂ :=
  ∑ i, ∑ j, W i j • ((finAdderMatrix Q r M i).conjTranspose * finAdderMatrix Q r M j)

lemma finTraceOperator_reindex (Q r M : ℕ) [NeZero Q]
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) :
    finTraceOperator Q r M W = tupleTraceOperator Q (liftedCoefficients W) := by
  symm
  simp only [tupleTraceOperator, finTraceOperator]
  apply Fintype.sum_equiv (indexEquiv r M)
  intro I
  apply Fintype.sum_equiv (indexEquiv r M)
  intro J
  simp [liftedCoefficients, finAdderMatrix]

/-- With zero diagonal, the full sum is exactly the off-diagonal definition. -/
lemma finTraceOperator_eq_offDiag (Q r M : ℕ) [NeZero Q]
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) (hD : ∀ i, W i i = 0) :
    finTraceOperator Q r M W =
      ∑ p : MatrixGrid.OffDiag (M^r), W p.1.1 p.1.2 •
        ((finAdderMatrix Q r M p.1.1).conjTranspose * finAdderMatrix Q r M p.1.2) := by
  classical
  let f : Fin (M^r) × Fin (M^r) → Matrix (TensorLabel Q r) (TensorLabel Q r) ℂ :=
    fun p => W p.1 p.2 • ((finAdderMatrix Q r M p.1).conjTranspose * finAdderMatrix Q r M p.2)
  have hs := Fintype.sum_subtype_add_sum_subtype (fun p : Fin (M^r) × Fin (M^r) => p.1 ≠ p.2) f
  have hd : (∑ p : {p : Fin (M^r) × Fin (M^r) // ¬ p.1 ≠ p.2}, f p.1) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have h : p.1.1 = p.1.2 := not_not.mp p.2
    simp [f, h, hD]
  rw [hd, add_zero] at hs
  simpa only [f, Fintype.sum_prod_type, finTraceOperator] using hs.symm

#print axioms finTraceOperator_reindex
#print axioms liftedCoefficients_energy

end
end AdderTrace


/-! Source component: MatrixCoefficientBounds.lean -/

open scoped BigOperators

namespace AdderTrace

lemma sum_coefficients_eq_offDiag {k : ℕ} {A : Type*} [AddCommMonoid A]
    (W : Matrix (Fin k) (Fin k) ℂ) (hD : ∀ i, W i i = 0)
    (f : ℂ → A) (hf : f 0 = 0) :
    (∑ p : Fin k × Fin k, f (W p.1 p.2)) =
      ∑ p : MatrixGrid.OffDiag k, f (W p.1.1 p.1.2) := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun p : Fin k × Fin k => p.1 ≠ p.2) (fun p => f (W p.1 p.2))
  have hd : (∑ p : {p : Fin k × Fin k // ¬ p.1 ≠ p.2}, f (W p.1.1 p.1.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have he : p.1.1 = p.1.2 := not_not.mp p.2
    simp [he, hD, hf]
  rw [hd, add_zero] at hs
  exact hs.symm

/-- Exact off-diagonal Cauchy--Schwarz coefficient bound needed in the
finite-word trace error, with k(k-1) rather than k^2. -/
theorem coefficient_l1_le_offDiag_energy {k : ℕ}
    (W : Matrix (Fin k) (Fin k) ℂ) (hD : ∀ i, W i i = 0) :
    (∑ p : Fin k × Fin k, ‖W p.1 p.2‖) ≤
      Real.sqrt (k*(k-1) : ℕ) * Real.sqrt (MatrixGrid.energy W) := by
  have h := coefficient_l1_le_sqrt_card_l2 (fun p : MatrixGrid.OffDiag k => W p.1.1 p.1.2)
  rw [MatrixGrid.offDiag_card] at h
  have h1 := sum_coefficients_eq_offDiag W hD (fun z => ‖z‖) (by simp)
  have h2 := sum_coefficients_eq_offDiag W hD (fun z => ‖z‖^2) (by simp)
  rw [← h1, ← h2] at h
  simpa only [MatrixGrid.energy, Complex.normSq_eq_norm_sq] using h

#print axioms coefficient_l1_le_offDiag_energy

end AdderTrace


/-! Source component: FullGrid.lean -/

open scoped BigOperators
namespace AdderTrace
namespace MatrixGrid
noncomputable section

def fullGridSet (k : ℕ) (C₁ : ℝ) : Set (Matrix (Fin k) (Fin k) ℂ) :=
  {W | (∀ i, W i i = 0) ∧ (∀ i j, W j i = star (W i j)) ∧
    IntegralEntries W ∧ 0 < (Matrix.trace (W ^ 2)).re ∧
      (Matrix.trace (W ^ 2)).re ≤ C₁ * (k : ℝ) ^ 2}

theorem fullGridSet_finite (k : ℕ) (C₁ : ℝ) (hk : 0 < k) (hC₁ : 0 < C₁) :
    (fullGridSet k C₁).Finite := by
  classical
  by_contra hinf
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
    ((2 * Nat.ceil (Real.sqrt C₁ * k)) ^ (k * (k - 1)) + 1)
  have hb := matrix_grid_card_le S C₁ hk hC₁
    (fun W hW => (hS hW).1)
    (fun W hW => (hS hW).2.1)
    (fun W hW => (hS hW).2.2.1)
    (fun W hW => (hS hW).2.2.2.2)
  omega

def fullGrid (k : ℕ) (C₁ : ℝ) (hk : 0 < k) (hC₁ : 0 < C₁) :
    Finset (Matrix (Fin k) (Fin k) ℂ) := (fullGridSet_finite k C₁ hk hC₁).toFinset

@[simp] theorem mem_fullGrid (k : ℕ) (C₁ : ℝ) (hk : 0 < k) (hC₁ : 0 < C₁)
    (W : Matrix (Fin k) (Fin k) ℂ) :
    W ∈ fullGrid k C₁ hk hC₁ ↔
      (∀ i, W i i = 0) ∧ (∀ i j, W j i = star (W i j)) ∧
        IntegralEntries W ∧ 0 < (Matrix.trace (W ^ 2)).re ∧
          (Matrix.trace (W ^ 2)).re ≤ C₁ * (k : ℝ) ^ 2 := by
  simp [fullGrid, fullGridSet]

theorem fullGrid_card_le (k : ℕ) (C₁ : ℝ) (hk : 0 < k) (hC₁ : 0 < C₁) :
    (fullGrid k C₁ hk hC₁).card ≤
      (2 * Nat.ceil (Real.sqrt C₁ * k)) ^ (k * (k - 1)) := by
  apply matrix_grid_card_le _ C₁ hk hC₁
  · intro W hW
    exact (mem_fullGrid k C₁ hk hC₁ W).mp hW |>.1
  · intro W hW
    exact (mem_fullGrid k C₁ hk hC₁ W).mp hW |>.2.1
  · intro W hW
    exact (mem_fullGrid k C₁ hk hC₁ W).mp hW |>.2.2.1
  · intro W hW
    exact (mem_fullGrid k C₁ hk hC₁ W).mp hW |>.2.2.2.2

end
end MatrixGrid
end AdderTrace


/-! Source component: FinalProposition.lean -/

/-! The exact matrix normalization and Gaussian-integer grid assembly.
The single raw-moment hypothesis is displayed explicitly; all scalar
normalization, coefficient estimates and grid cardinality are proved. -/

open scoped BigOperators

set_option maxHeartbeats 200000

namespace AdderTrace

noncomputable def offDiagL1 {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ) : ℝ :=
  ∑ p : MatrixGrid.OffDiag k, ‖W p.val.1 p.val.2‖

theorem offDiag_energy {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ)
    (hD : ∀ i, W i i = 0) :
    (∑ p : MatrixGrid.OffDiag k, ‖W p.val.1 p.val.2‖ ^ 2) = MatrixGrid.energy W := by
  classical
  apply Fintype.sum_of_injective
    (fun p : MatrixGrid.OffDiag k => p.val) Subtype.val_injective
  · intro p hp
    have hdiag : p.1 = p.2 := by
      by_contra hn
      exact hp ⟨⟨p, hn⟩, rfl⟩
    simp [hdiag, hD]
  · intro p
    simp [Complex.normSq_eq_norm_sq]

theorem offDiagL1_le_trace_sqrt {k : ℕ} (hk : 0 < k)
    (W : Matrix (Fin k) (Fin k) ℂ)
    (hD : ∀ i, W i i = 0) (hH : ∀ i j, W j i = star (W i j)) :
    offDiagL1 W ≤ Real.sqrt (Matrix.trace (W ^ 2)).re *
      Real.sqrt ((k : ℝ) * ((k : ℝ) - 1)) := by
  have h := coefficient_l1_le_sqrt_card_l2
    (fun p : MatrixGrid.OffDiag k => W p.val.1 p.val.2)
  rw [MatrixGrid.offDiag_card, offDiag_energy W hD,
    MatrixGrid.energy_eq_trace_sq W hH] at h
  have hc : ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  simpa only [offDiagL1, hc, mul_comm] using h

theorem trace_sqrt_le_grid_radius {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ)
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hT : (Matrix.trace (W ^ 2)).re ≤ C₁ * (k : ℝ) ^ 2) :
    Real.sqrt (Matrix.trace (W ^ 2)).re ≤ Real.sqrt C₁ * k := by
  calc
    _ ≤ Real.sqrt (C₁ * (k : ℝ) ^ 2) := Real.sqrt_le_sqrt hT
    _ = _ := by rw [Real.sqrt_mul hC₁, Real.sqrt_sq (Nat.cast_nonneg k)]

/-- Scalar normalization of an actual matrix power and its normalized trace. -/
theorem normalizedTrace_scaled_pow {N : Type*} [Fintype N] [DecidableEq N]
    (A : Matrix N N ℂ) (c : ℝ) (m : ℕ) :
    normalizedTrace ((((c⁻¹ : ℝ) : ℂ) • A) ^ m) =
      normalizedTrace (A ^ m) / c ^ m := by
  rw [smul_pow]
  simp only [normalizedTrace, Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, inv_pow]
  ring

theorem sqrt_grid_coefficient (k : ℕ) (hk : 0 < k) (C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    Real.sqrt C₁ * Real.sqrt ((k : ℝ) * ((k : ℝ) - 1)) =
      Real.sqrt (C₁ * k * (k - 1 : ℕ)) := by
  rw [← Real.sqrt_mul hC₁]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  ring

/-- The exact bound in the proposition follows from the raw even-moment
estimate.  Grid cardinality and all normalization steps are discharged. -/
theorem filter_bound_of_raw_moments
    {k : ℕ} {N : Type*} [Fintype N] [DecidableEq N]
    (S : Finset (Matrix (Fin k) (Fin k) ℂ)) (U : Fin k → Matrix N N ℂ)
    (C₁ C₂ D ε : ℝ) (L : ℕ)
    (hk : 0 < k) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hdiag : ∀ W ∈ S, ∀ i, W i i = 0)
    (hherm : ∀ W ∈ S, ∀ i j, W j i = star (W i j))
    (hintegral : ∀ W ∈ S, MatrixGrid.IntegralEntries W)
    (hgrid : ∀ W ∈ S, (Matrix.trace (W ^ 2)).re ≤ C₁ * (k : ℝ) ^ 2)
    (hmoment : ∀ W ∈ S,
      normalizedTrace (momentMatrix U W ^ (2 * L)) ≤
        (D * Real.sqrt (Matrix.trace (W ^ 2)).re) ^ (2 * L) +
          ε * offDiagL1 W ^ (2 * L)) :
    normalizedTrace (filterMatrix S U (C₂ * k) L) ≤
      ((2 * Nat.ceil (Real.sqrt C₁ * k)) ^ (k * (k - 1)) : ℕ) *
        ((Real.sqrt C₁ * D / C₂) ^ (2 * L) +
          ε * (Real.sqrt (C₁ * k * (k - 1 : ℕ)) / C₂) ^ (2 * L)) := by
  apply filter_bound_of_pointwise_and_card
  · positivity
  · exact MatrixGrid.matrix_grid_card_le S C₁ hk hC₁ hdiag hherm hintegral hgrid
  · intro W hW
    rw [normalizedTrace_scaled_pow]
    have hx0 : 0 ≤ Real.sqrt (Matrix.trace (W ^ 2)).re := Real.sqrt_nonneg _
    have hy0 : 0 ≤ offDiagL1 W := by
      unfold offDiagL1
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hx := trace_sqrt_le_grid_radius W C₁ (le_of_lt hC₁) (hgrid W hW)
    have hy := offDiagL1_le_trace_sqrt hk W (hdiag W hW) (hherm W hW)
    have h : normalizedTrace (momentMatrix U W ^ (2 * L)) / (C₂ * (k : ℝ)) ^ (2 * L) ≤
        (Real.sqrt C₁ * D / C₂) ^ (2 * L) +
          ε * (Real.sqrt C₁ * Real.sqrt ((k : ℝ) * ((k : ℝ) - 1)) / C₂) ^ (2 * L) := by
      apply normalize_moment_bound
        (normalizedTrace (momentMatrix U W ^ (2 * L)))
        (Real.sqrt (Matrix.trace (W ^ 2)).re) (offDiagL1 W)
        D (Real.sqrt C₁) (k : ℝ) C₂ ε (2 * L)
      · exact hD
      · exact_mod_cast hk
      · exact hC₂
      · exact hε
      · exact hx0
      · exact hy0
      · exact hx
      · exact hy
      · exact hmoment W hW
    simpa only [sqrt_grid_coefficient k hk C₁ (le_of_lt hC₁)] using h

/-- Specialization to the exact k=M^r, Delta_r, and B_L/Q constants. -/
theorem explicit_filter_bound_of_raw_moments
    {N : Type*} [Fintype N] [DecidableEq N]
    (M r L Q : ℕ) (C₁ C₂ : ℝ)
    (S : Finset (Matrix (Fin (M ^ r)) (Fin (M ^ r)) ℂ))
    (U : Fin (M ^ r) → Matrix N N ℂ)
    (hM : 0 < M) (hQ : 0 < Q) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hdiag : ∀ W ∈ S, ∀ i, W i i = 0)
    (hherm : ∀ W ∈ S, ∀ i j, W j i = star (W i j))
    (hintegral : ∀ W ∈ S, MatrixGrid.IntegralEntries W)
    (hgrid : ∀ W ∈ S,
      (Matrix.trace (W ^ 2)).re ≤ C₁ * ((M ^ r : ℕ) : ℝ) ^ 2)
    (hmoment : ∀ W ∈ S,
      normalizedTrace (momentMatrix U W ^ (2 * L)) ≤
        (delta M r * Real.sqrt (Matrix.trace (W ^ 2)).re) ^ (2 * L) +
          ((wordBound M L : ℝ) / Q) * offDiagL1 W ^ (2 * L)) :
    normalizedTrace (filterMatrix S U (C₂ * (M ^ r : ℕ)) L) ≤
      traceRHS C₁ C₂ M r L Q := by
  simpa only [traceRHS] using
    filter_bound_of_raw_moments S U C₁ C₂ (delta M r) ((wordBound M L : ℝ) / Q) L
      (pow_pos hM r) hC₁ hC₂ (Real.sqrt_nonneg _)
      (div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_of_lt hQ))
      hdiag hherm hintegral hgrid hmoment

/-- The filter is summed over the complete grid in the proposition.
Only the raw moment estimate remains as an input to this assembly lemma. -/
theorem full_grid_filter_bound_of_raw_moments
    {N : Type*} [Fintype N] [DecidableEq N]
    (M r L Q : ℕ) (C₁ C₂ : ℝ)
    (U : Fin (M ^ r) → Matrix N N ℂ)
    (hM : 0 < M) (hQ : 0 < Q) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hmoment : ∀ W : Matrix (Fin (M ^ r)) (Fin (M ^ r)) ℂ,
      (∀ i, W i i = 0) → (∀ i j, W j i = star (W i j)) →
      normalizedTrace (momentMatrix U W ^ (2 * L)) ≤
        (delta M r * Real.sqrt (Matrix.trace (W ^ 2)).re) ^ (2 * L) +
          ((wordBound M L : ℝ) / Q) * offDiagL1 W ^ (2 * L)) :
    normalizedTrace
      (filterMatrix (MatrixGrid.fullGrid (M ^ r) C₁ (pow_pos hM r) hC₁)
        U (C₂ * (M ^ r : ℕ)) L) ≤ traceRHS C₁ C₂ M r L Q := by
  apply explicit_filter_bound_of_raw_moments M r L Q C₁ C₂ _ U hM hQ hC₁ hC₂
  · intro W hW
    exact ((MatrixGrid.mem_fullGrid _ _ _ _ W).mp hW).1
  · intro W hW
    exact ((MatrixGrid.mem_fullGrid _ _ _ _ W).mp hW).2.1
  · intro W hW
    exact ((MatrixGrid.mem_fullGrid _ _ _ _ W).mp hW).2.2.1
  · intro W hW
    exact ((MatrixGrid.mem_fullGrid _ _ _ _ W).mp hW).2.2.2.2
  · intro W hW
    have hg := (MatrixGrid.mem_fullGrid _ _ _ _ W).mp hW
    exact hmoment W hg.1 hg.2.1

#print axioms normalizedTrace_scaled_pow
#print axioms filter_bound_of_raw_moments
#print axioms explicit_filter_bound_of_raw_moments
#print axioms full_grid_filter_bound_of_raw_moments

end AdderTrace


/-! Source component: ReindexedMoments.lean -/

open scoped BigOperators

namespace AdderTrace

lemma liftedCoefficients_l1_offDiag {r M : ℕ}
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) (hD : ∀ i, W i i = 0) :
    (∑ I, ∑ J, ‖liftedCoefficients W I J‖) = offDiagL1 W := by
  rw [liftedCoefficients_l1]
  exact sum_coefficients_eq_offDiag W hD (fun z => ‖z‖) (by simp)

lemma momentMatrix_fin_eq (Q r M : ℕ) [NeZero Q]
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) (hD : ∀ i, W i i = 0) :
    momentMatrix (finAdderMatrix Q r M) W = finTraceOperator Q r M W := by
  classical
  unfold momentMatrix finTraceOperator
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i = j
  · subst j
    simp [hD]
  · simp [h]

lemma momentMatrix_reindex (Q r M : ℕ) [NeZero Q]
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ) (hD : ∀ i, W i i = 0) :
    momentMatrix (finAdderMatrix Q r M) W =
      momentMatrix (tensorAdderMatrix Q) (liftedCoefficients W) := by
  rw [momentMatrix_fin_eq Q r M W hD, finTraceOperator_reindex,
    momentMatrix_eq_full_sum Q r M (liftedCoefficients W) (liftedCoefficients_diagonal W hD)]
  rfl

/-- The complete concrete finite-to-free moment comparison in the Fin k
indexing used by the Gaussian-integer grid. Only the free moment remains
on the right; the adder and trace discrepancy bounds are all proved. -/
theorem concrete_fin_moment_re_le (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ)
    (hD : ∀ i, W i i = 0) :
    normalizedTrace ((momentMatrix (finAdderMatrix Q r M) W) ^ (2*L)) ≤
      ‖(ExplicitFilter.freePolynomial (liftedCoefficients W) ^ (2*L)) 1‖ +
      (wordBound M L : ℝ)/(Q:ℝ) * offDiagL1 W ^ (2*L) := by
  rw [momentMatrix_reindex Q r M W hD]
  have h := concrete_moment_re_le Q r M L hM (liftedCoefficients W)
    (liftedCoefficients_diagonal W hD)
  rw [liftedCoefficients_l1_offDiag W hD] at h
  exact h

#print axioms concrete_fin_moment_re_le

end AdderTrace


/-! Source component: FilterReality.lean -/

open scoped BigOperators
namespace AdderTrace

variable {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]

theorem momentMatrix_conjTranspose (U : K → Matrix N N ℂ)
    (W : Matrix K K ℂ) (hW : ∀ i j, W j i = star (W i j)) :
    (momentMatrix U W).conjTranspose = momentMatrix U W := by
  classical
  unfold momentMatrix
  simp only [Matrix.conjTranspose_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      hW j i]

theorem filterMatrix_conjTranspose (S : Finset (Matrix K K ℂ))
    (U : K → Matrix N N ℂ) (c : ℝ) (L : ℕ)
    (hW : ∀ W ∈ S, ∀ i j, W j i = star (W i j)) :
    (filterMatrix S U c L).conjTranspose = filterMatrix S U c L := by
  unfold filterMatrix
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro W hWS
  rw [Matrix.conjTranspose_pow, Matrix.conjTranspose_smul,
    momentMatrix_conjTranspose U W (hW W hWS)]
  simp

theorem filter_trace_real (S : Finset (Matrix K K ℂ))
    (U : K → Matrix N N ℂ) (c : ℝ) (L : ℕ)
    (hW : ∀ W ∈ S, ∀ i j, W j i = star (W i j)) :
    ((Matrix.trace (filterMatrix S U c L)).re : ℂ) =
      Matrix.trace (filterMatrix S U c L) := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace (filterMatrix S U c L)) = _
  rw [← Matrix.trace_conjTranspose, filterMatrix_conjTranspose S U c L hW]

#print axioms filter_trace_real
end AdderTrace


/-! Source component: TechnicalTrace.lean -/

/-! Complete trace proposition for the explicitly prescribed modular
adder circuits.  No moment, norm, freeness, or counting bound is assumed. -/

namespace AdderTrace

/-- The unconditional raw matrix-moment estimate in the Fin k indexing
used by the Gaussian-integer grid. -/
theorem finite_adder_raw_moment_bound (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (W : Matrix (Fin (M ^ r)) (Fin (M ^ r)) ℂ)
    (hdiag : ∀ i, W i i = 0) (hH : ∀ i j, W j i = star (W i j)) :
    normalizedTrace (momentMatrix (finAdderMatrix Q r M) W ^ (2 * L)) ≤
      (delta M r * Real.sqrt (Matrix.trace (W ^ 2)).re) ^ (2 * L) +
        (wordBound M L : ℝ) / Q * offDiagL1 W ^ (2 * L) := by
  have hfinite := concrete_fin_moment_re_le Q r M L hM W hdiag
  have hfree := free_polynomial_even_moment_bound r M L hM
    (liftedCoefficients W) (liftedCoefficients_diagonal W hdiag)
  rw [liftedCoefficients_energy, MatrixGrid.energy_eq_trace_sq W hH] at hfree
  exact hfinite.trans (add_le_add_right hfree _)

/-- The exact filter in the question, with Q=2^q, k=M^r, and n=Q^(2r).
The finite set is the entire Gaussian-integer Hermitian grid. -/
noncomputable def prescribedFilter (M r L q : ℕ) (C₁ C₂ : ℝ)
    (hM : 2 ≤ M) (hC₁ : 2 < C₁) :
    Matrix (TensorLabel (2 ^ q) r) (TensorLabel (2 ^ q) r) ℂ :=
  filterMatrix
    (MatrixGrid.fullGrid (M ^ r) C₁ (pow_pos (by omega : 0 < M) r) (by linarith))
    (finAdderMatrix (2 ^ q) r M) (C₂ * (M ^ r : ℕ)) L

/-- The filter trace is genuinely real; the real part in the ordered
inequality below therefore denotes the actual trace. -/
theorem prescribedFilter_trace_real (M r L q : ℕ) (C₁ C₂ : ℝ)
    (hM : 2 ≤ M) (hC₁ : 2 < C₁) :
    ((Matrix.trace (prescribedFilter M r L q C₁ C₂ hM hC₁)).re : ℂ) =
      Matrix.trace (prescribedFilter M r L q C₁ C₂ hM hC₁) := by
  unfold prescribedFilter
  apply filter_trace_real
  intro W hW
  exact ((MatrixGrid.mem_fullGrid _ _ _ _ W).mp hW).2.1

/-- The proposition as stated in the question.  All bounds are proved
for the actual adders; the only hypotheses are the stated parameters.
Several size assumptions are stronger than the proof needs, but are
retained here to match the original statement exactly. -/
theorem technical_trace_bound
    (M r L q : ℕ) (C₁ C₂ : ℝ)
    (hM : 2 ≤ M) (_hr : 1 ≤ r) (_hL : 1 ≤ L) (_hq : 1 ≤ q)
    (hC₁ : 2 < C₁) (hC₂ : Real.sqrt C₁ * delta M r < C₂)
    (_hQ : wordBound M L < 2 ^ q) :
    (Matrix.trace (prescribedFilter M r L q C₁ C₂ hM hC₁)).re /
      ((2 ^ q : ℕ) : ℝ) ^ (2 * r) ≤ traceRHS C₁ C₂ M r L (2 ^ q) := by
  have hMpos : 0 < M := by omega
  have hQpos : 0 < (2 : ℕ) ^ q := pow_pos (by decide) q
  have hC₁pos : 0 < C₁ := by linarith
  have hC₂pos : 0 < C₂ :=
    lt_of_le_of_lt (mul_nonneg (Real.sqrt_nonneg C₁) (Real.sqrt_nonneg _)) hC₂
  have h := full_grid_filter_bound_of_raw_moments M r L (2 ^ q) C₁ C₂
    (finAdderMatrix (2 ^ q) r M) hMpos hQpos hC₁pos hC₂pos
    (fun W hdiag hH => finite_adder_raw_moment_bound (2 ^ q) r M L hM W hdiag hH)
  simpa only [prescribedFilter, normalizedTrace, tensorLabel_card, Nat.cast_pow] using h

#print axioms finite_adder_raw_moment_bound
#print axioms prescribedFilter_trace_real
#print axioms technical_trace_bound

end AdderTrace


/-! Source component: AdderCircuits.lean -/

namespace AdderTrace

/-- Integer powers of the upper modular shear, as actual permutations. -/
def modularUpper (Q : ℕ) (s : ℤ) : Equiv.Perm (ZMod Q × ZMod Q) where
  toFun := labelAction Q (shearA s)
  invFun := labelAction Q (shearA (-s))
  left_inv x := by rw [← labelAction_mul, shearA_add, neg_add_cancel, shearA_zero, labelAction_one]
  right_inv x := by rw [← labelAction_mul, shearA_add, add_neg_cancel, shearA_zero, labelAction_one]

/-- Integer powers of the lower modular shear, as actual permutations. -/
def modularLower (Q : ℕ) (s : ℤ) : Equiv.Perm (ZMod Q × ZMod Q) where
  toFun := labelAction Q (shearB s)
  invFun := labelAction Q (shearB (-s))
  left_inv x := by rw [← labelAction_mul, shearB_add, neg_add_cancel, shearB_zero, labelAction_one]
  right_inv x := by rw [← labelAction_mul, shearB_add, add_neg_cancel, shearB_zero, labelAction_one]

/-- ADD_{B→A} from the proposition. -/
def addBtoA (Q : ℕ) : Equiv.Perm (ZMod Q × ZMod Q) := modularUpper Q 1
/-- ADD_{A→B} from the proposition. -/
def addAtoB (Q : ℕ) : Equiv.Perm (ZMod Q × ZMod Q) := modularLower Q 1

@[simp] theorem addBtoA_apply (Q : ℕ) (a b : ZMod Q) :
    addBtoA Q (a,b) = (a+2*b,b) := by
  simp [addBtoA, modularUpper, labelAction, shearA]

@[simp] theorem addAtoB_apply (Q : ℕ) (a b : ZMod Q) :
    addAtoB Q (a,b) = (a,b+2*a) := by
  simp [addAtoB, modularLower, labelAction, shearB, add_comm]

lemma modularUpper_add (Q : ℕ) (s t : ℤ) :
    modularUpper Q (s+t) = modularUpper Q s * modularUpper Q t := by
  apply Equiv.ext
  intro x
  change labelAction Q (shearA (s+t)) x = labelAction Q (shearA s) (labelAction Q (shearA t) x)
  rw [← labelAction_mul, shearA_add]

@[simp] lemma modularUpper_zero (Q : ℕ) : modularUpper Q 0 = 1 := by
  apply Equiv.ext
  intro x
  change labelAction Q (shearA 0) x = x
  rw [shearA_zero, labelAction_one]

lemma modularUpper_nat (Q i : ℕ) : modularUpper Q (i : ℤ) = (addBtoA Q)^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.cast_add, Nat.cast_one, modularUpper_add, ih, pow_succ]
    rfl

lemma modularUpper_neg (Q : ℕ) (s : ℤ) : modularUpper Q (-s) = (modularUpper Q s)⁻¹ := by
  apply Equiv.ext
  intro x
  rfl

/-- Exact identification of the construction with the two requested circuits. -/
theorem modularStepPerm_circuit (Q i : ℕ) :
    modularStepPerm Q i 1 =
      (addBtoA Q)^i * addAtoB Q * ((addBtoA Q)^i)⁻¹ := by
  rw [← modularUpper_nat, ← modularUpper_neg]
  apply Equiv.ext
  intro x
  change labelAction Q (shearA (i:ℤ)*shearB 1*shearA (-(i:ℤ))) x =
    labelAction Q (shearA (i:ℤ)) (labelAction Q (shearB 1) (labelAction Q (shearA (-(i:ℤ))) x))
  simp only [labelAction_mul]

/-- Tensor adders act independently on the two-register label of each coordinate. -/
theorem tensorAdder_apply (Q : ℕ) {r M : ℕ} (I : AdderIndex r M)
    (x : TensorLabel Q r) (s : Fin r) :
    tensorAdder Q I x s = modularStepPerm Q (I s).val 1 (x s) := by
  change modularRepresentation Q (FreeGroup.map Fin.val (FreeGroup.of (I s))) (x s) = _
  rw [FreeGroup.map.of, modularRepresentation_of]

/-- The concrete matrices satisfy both defining unitary identities. -/
theorem tensorAdderMatrix_unitary (Q : ℕ) [NeZero Q] {r M : ℕ} (I : AdderIndex r M) :
    (tensorAdderMatrix Q I).conjTranspose * tensorAdderMatrix Q I = 1 ∧
      tensorAdderMatrix Q I * (tensorAdderMatrix Q I).conjTranspose = 1 := by
  simp only [tensorAdderMatrix, permutationMatrix_conjTranspose, ← permutationMatrix_mul,
    inv_mul_cancel, mul_inv_cancel, permutationMatrix_one, and_self]

#print axioms modularStepPerm_circuit
#print axioms tensorAdderMatrix_unitary

end AdderTrace

/-! Kernel dependency audit: reject every nonstandard axiom, including any
proof placeholder, in every theorem declared in our namespaces. -/
run_cmd do
  let env ← Lean.getEnv
  let count ← env.constants.foldM (init := (0 : Nat)) fun count name info => do
    let relevant := name.toString.startsWith "AdderTrace." ||
      name.toString.startsWith "AdderCones." || name.toString.startsWith "ExplicitFilter."
    match info with
    | .thmInfo _ =>
      if relevant then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Unexpected axiom {ax} in {name}"
        return count + 1
      else return count
    | _ => return count
  Lean.logInfo m!"AXIOM AUDIT PASSED: {count} theorems; only propext, Classical.choice, Quot.sound."
