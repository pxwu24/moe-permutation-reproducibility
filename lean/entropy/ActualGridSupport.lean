import ActualGridFilterLower
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A. Support estimate for the actual finite-grid filter

This standalone verification assembles Gaussian-integer rounding, the
noncommutative spectral filter, and the zero-diagonal real-linear observable.
The net and filtered norm estimates are proved for the actual grid.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open ComplexOrder

namespace ActualGridSupport

variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-- The real vector space of zero-diagonal Hermitian test matrices. -/
def zeroDiagonal (k : ℕ) : Submodule ℝ (HermitianMat (Fin k) ℂ) where
  carrier := {W | ∀ i, W i i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro W V hW hV i
    change W i i + V i i = 0
    rw [hW, hV, add_zero]
  smul_mem' := by
    intro c W hW i
    change c • W i i = 0
    rw [hW, smul_zero]

/-- The user's support observable as an actual real-linear matrix-valued map. -/
def observableLinear (U : Fin k → Matrix d d ℂ) :
    HermitianMat (Fin k) ℂ →ₗ[ℝ] Matrix d d ℂ where
  toFun W := (GaussianSignCoefficient.observable U W).mat
  map_add' W V := by
    change (∑ i, ∑ j, (W i j + V i j) • ((U i).conjTranspose * U j)) = _
    simp only [add_smul, Finset.sum_add_distrib]
    rfl
  map_smul' c W := by
    change (∑ i, ∑ j, (c • W i j) • ((U i).conjTranspose * U j)) =
      c • (∑ i, ∑ j, W i j • ((U i).conjTranspose * U j))
    simp only [smul_assoc, Finset.smul_sum]

/-- Restrict the observable to the zero-diagonal Hermitian subspace. -/
def observableCLM (U : Fin k → Matrix d d ℂ) :
    zeroDiagonal k →L[ℝ] Matrix d d ℂ :=
  ((observableLinear U).comp (zeroDiagonal k).subtype).toContinuousLinearMap

/-- The actual Gaussian-integer filter index. -/
abbrev GridIndex (C₁ : ℝ) (k : ℕ) :=
  {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W}

/-- The normalized real-linear grid point used in the rounding net. -/
def gridPoint (C₁ : ℝ) (W : GridIndex C₁ k) : zeroDiagonal k :=
  ⟨((Real.sqrt C₁ * (k : ℝ))⁻¹ : ℝ) • W.val, by
    intro i
    change ((Real.sqrt C₁ * (k : ℝ))⁻¹ : ℝ) • W.val i i = 0
    rw [W.property.1, smul_zero]⟩

/-- The normalized Hermitian observables entering the actual filter. -/
def gridObservable (C₁ C₂ : ℝ) (U : Fin k → Matrix d d ℂ)
    (W : GridIndex C₁ k) : HermitianMat d ℂ :=
  (C₂ * (k : ℝ))⁻¹ • GaussianSignCoefficient.observable U W.val

/-- The positive suppressing operator from the actual finite-grid filter. -/
def fullGridH (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ) (L : ℕ) (γ : ℝ) : HermitianMat d ℂ :=
  Real.sqrt γ • (1 + ActualGridFilterLower.fullGridFilter C₁ hC₁ hk C₂ U L)⁻¹.sqrt

/-- The proved Gaussian rounding net lies in the zero-diagonal subspace. -/
lemma actual_grid_net (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (X : zeroDiagonal k) (hX : ‖X‖ = 1) :
    ∃ W : GridIndex C₁ k,
      ‖X - gridPoint C₁ W‖ ≤ Real.sqrt 2 / Real.sqrt C₁ := by
  obtain ⟨W, hW, _, hclose⟩ :=
    GaussianHermitianGrid.grid_net C₁ hC₁ hk X.val X.property hX
  exact ⟨⟨W, hW⟩, hclose⟩

omit [DecidableEq d] in
/-- The normalization of the actual grid agrees with the filter normalization. -/
lemma observable_gridPoint (C₁ C₂ : ℝ) (hC₁ : 2 < C₁) (hC₂ : 0 < C₂)
    (hk : 2 ≤ k) (U : Fin k → Matrix d d ℂ) (W : GridIndex C₁ k) :
    observableCLM U (gridPoint C₁ W) =
      (C₂ / Real.sqrt C₁) • (gridObservable C₁ C₂ U W).mat := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have ha0 : Real.sqrt C₁ ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  change observableLinear U (((Real.sqrt C₁ * (k : ℝ))⁻¹ : ℝ) • W.val) = _
  rw [map_smul]
  change ((Real.sqrt C₁ * (k : ℝ))⁻¹ : ℝ) •
      (GaussianSignCoefficient.observable U W.val).mat =
    (C₂ / Real.sqrt C₁) • ((C₂ * (k : ℝ))⁻¹ •
      (GaussianSignCoefficient.observable U W.val).mat)
  rw [smul_smul]
  congr 1
  field_simp [hC₂.ne', ha0, hk0]

/-- The exact actual-grid support estimate for every zero-diagonal Hermitian
test matrix.  No unitarity, moment, trace, or net hypotheses are needed. -/
lemma actual_grid_support_bound (C₁ C₂ : ℝ) (hC₁ : 2 < C₁) (hC₂ : 0 < C₂)
    (hk : 2 ≤ k) (U : Fin k → Matrix d d ℂ) (L : ℕ) (hL : 1 ≤ L)
    (γ : ℝ) (hγ : 0 ≤ γ) (W : HermitianMat (Fin k) ℂ) (hW : ∀ i, W i i = 0) :
    ‖(fullGridH C₁ hC₁ hk C₂ U L γ).mat *
        (GaussianSignCoefficient.observable U W).mat *
          (fullGridH C₁ hC₁ hk C₂ U L γ).mat‖ ≤
      C₂ * γ / (Real.sqrt C₁ - Real.sqrt 2) * ‖W‖ := by
  let : Fintype (GridIndex C₁ k) :=
    (GaussianHermitianGrid.grid_finite C₁ (by linarith) (by omega)).fintype
  have ha : 0 < Real.sqrt C₁ := Real.sqrt_pos.mpr (by linarith)
  have hlt : Real.sqrt 2 < Real.sqrt C₁ := Real.sqrt_lt_sqrt (by norm_num) hC₁
  have hδ : 0 ≤ Real.sqrt 2 / Real.sqrt C₁ := by positivity
  have hδ1 : Real.sqrt 2 / Real.sqrt C₁ < 1 := (div_lt_one ha).mpr hlt
  have hb := FiniteFilterSupport.finite_filter_net_bound
    (observableCLM U) (gridPoint C₁) (gridObservable C₁ C₂ U) L hL
    (C₂ / Real.sqrt C₁) γ (Real.sqrt 2 / Real.sqrt C₁)
    (by positivity) hγ hδ hδ1
    (observable_gridPoint C₁ C₂ hC₁ hC₂ hk U)
    (actual_grid_net C₁ hC₁ hk) (⟨W, hW⟩ : zeroDiagonal k)
  have hc : γ * (C₂ / Real.sqrt C₁) / (1 - Real.sqrt 2 / Real.sqrt C₁) =
      C₂ * γ / (Real.sqrt C₁ - Real.sqrt 2) := by
    field_simp [ha.ne', (sub_pos.mpr hlt).ne']
  rw [hc] at hb
  exact hb

#print axioms actual_grid_net
#print axioms observable_gridPoint
#print axioms actual_grid_support_bound

end ActualGridSupport
