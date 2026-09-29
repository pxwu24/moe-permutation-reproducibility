import GaussianSignCoefficient
import GaussianSignGrid

/-!
# A. Lower bound for the actual Gaussian-grid filter

This file assembles the exact Gaussian-integer grid, the sign-test embedding,
the coefficient identity, and the noncommutative moment lower bound.  Its
conclusion is about the actual filter sum, not an abstract presumed subfamily.
-/

noncomputable section
open scoped BigOperators
open ComplexOrder

namespace ActualGridFilterLower

variable {d : Type*} [Fintype d] [DecidableEq d] {k : ℕ}

/-- The user's full finite filter, summed over exactly the Gaussian-integer
zero-diagonal Hermitian grid. -/
def fullGridFilter (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ) (L : ℕ) : HermitianMat d ℂ :=
  let : Fintype {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W} :=
    (GaussianHermitianGrid.grid_finite C₁ (by linarith) (by omega)).fintype
  FiniteFilterSupport.filter
    (fun W : {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W} =>
      (C₂ * (k : ℝ))⁻¹ • GaussianSignCoefficient.observable U W.val) L

/-- Every actual full-grid filter dominates the Gaussian-sign barrier.  All
subfamily membership, injection, coefficient, and moment facts are proved. -/
lemma full_grid_filter_lower_edges (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (U : Fin k → Matrix d d ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (hU' : ∀ i, U i * (U i).conjTranspose = 1) (L : ℕ) :
    ((2 : ℝ) ^ (2 * Fintype.card (GaussianSignGrid.UpperEdge k)) *
        (4 * (Fintype.card (GaussianSignGrid.UpperEdge k) : ℝ) *
          ((C₂ * (k : ℝ))⁻¹) ^ 2) ^ L) • (1 : HermitianMat d ℂ) ≤
      fullGridFilter C₁ hC₁ hk C₂ U L := by
  classical
  let : Fintype {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W} :=
    (GaussianHermitianGrid.grid_finite C₁ (by linarith) (by omega)).fintype
  let Z := fun W : {W : HermitianMat (Fin k) ℂ // GaussianHermitianGrid.InGrid C₁ W} =>
    (C₂ * (k : ℝ))⁻¹ • GaussianSignCoefficient.observable U W.val
  let V : GaussianSignGrid.UpperEdge k → Matrix d d ℂ :=
    GaussianSignCoefficient.edgeWord U
  have hV (e : GaussianSignGrid.UpperEdge k) :=
    GaussianSignCoefficient.pair_word_unitary
      (U e.val.1) (U e.val.2) (hU _) (hU' _) (hU _) (hU' _)
  apply SignFilterLower.full_filter_gaussian_sign_lower Z V
    (fun e => (hV e).1) (fun e => (hV e).2)
    (GaussianSignGrid.gridEmbedding C₁ hC₁ hk) ((C₂ * (k : ℝ))⁻¹) L
  intro σ
  change (C₂ * (k : ℝ))⁻¹ •
      GaussianSignCoefficient.observable U (GaussianSignGrid.signedHermitian σ) = _
  congr 1
  apply GaussianSignCoefficient.observable_eq_signed_quadratures
    U (GaussianSignGrid.signedHermitian σ) (GaussianSignGrid.signedHermitian_diag σ) σ
  intro e
  rw [GaussianSignGrid.signedHermitian_upper σ _ _ e.property]
  rfl

/-- The exact scalar lower bound in terms of the user's output dimension `k`
and filter-normalization constant `C₂`. -/
lemma full_grid_filter_lower (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (hC₂ : 0 < C₂) (U : Fin k → Matrix d d ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (hU' : ∀ i, U i * (U i).conjTranspose = 1) (L : ℕ) :
    ((2 : ℝ) ^ (k * (k - 1)) *
        (2 * (1 - 1 / (k : ℝ)) / C₂ ^ 2) ^ L) • (1 : HermitianMat d ℂ) ≤
      fullGridFilter C₁ hC₁ hk C₂ U L := by
  have he := full_grid_filter_lower_edges C₁ hC₁ hk C₂ U hU hU' L
  rw [GaussianSignGrid.twice_upperEdge_card] at he
  have hc : 2 * (Fintype.card (GaussianSignGrid.UpperEdge k) : ℝ) =
      (k : ℝ) * ((k : ℝ) - 1) := by
    have hn := GaussianSignGrid.twice_upperEdge_card (k := k)
    have hn' : 2 * (Fintype.card (GaussianSignGrid.UpperEdge k) : ℝ) =
        (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one] using hn'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hb : 4 * (Fintype.card (GaussianSignGrid.UpperEdge k) : ℝ) *
      ((C₂ * (k : ℝ))⁻¹) ^ 2 = 2 * (1 - 1 / (k : ℝ)) / C₂ ^ 2 := by
    have hc' : 4 * (Fintype.card (GaussianSignGrid.UpperEdge k) : ℝ) =
        2 * (k : ℝ) * ((k : ℝ) - 1) := by nlinarith [hc]
    rw [hc']
    field_simp [hC₂.ne', hk0]
  rw [hb] at he
  exact he

/-- The actual normalized trace of the filter is at least the same barrier. -/
lemma full_grid_filter_trace_lower [Nonempty d]
    (C₁ : ℝ) (hC₁ : 2 < C₁) (hk : 2 ≤ k)
    (C₂ : ℝ) (hC₂ : 0 < C₂) (U : Fin k → Matrix d d ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (hU' : ∀ i, U i * (U i).conjTranspose = 1) (L : ℕ) :
    (2 : ℝ) ^ (k * (k - 1)) * (2 * (1 - 1 / (k : ℝ)) / C₂ ^ 2) ^ L ≤
      (fullGridFilter C₁ hC₁ hk C₂ U L).trace / (Fintype.card d : ℝ) := by
  have hm := full_grid_filter_lower C₁ hC₁ hk C₂ hC₂ U hU hU' L
  have ht := HermitianMat.trace_nonneg (sub_nonneg.mpr hm)
  rw [HermitianMat.trace_sub, HermitianMat.trace_smul, HermitianMat.trace_one] at ht
  apply (le_div_iff₀ (show (0 : ℝ) < Fintype.card d by exact_mod_cast Fintype.card_pos)).mpr
  linarith

#print axioms full_grid_filter_lower_edges
#print axioms full_grid_filter_lower
#print axioms full_grid_filter_trace_lower

end ActualGridFilterLower
