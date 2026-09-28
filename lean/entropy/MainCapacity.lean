import MainHolevoTensor

/-!
The regularized Holevo formula for classical capacity, built from actual tensor
powers of the channel. This file proves the two-copy lower bound directly from
the supremum. The operational coding theorem identifying this regularization
with achievable communication rates is not re-proved here.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace MainCapacity
open MainHolevo

/-- The basis of a positive tensor power: `TensorBasis d t` has t+1 factors. -/
def TensorBasis (d : Type) : ℕ → Type
  | 0 => d
  | t + 1 => d × TensorBasis d t

instance repeatFintype (d : Type) [Fintype d] : (t : ℕ) → Fintype (TensorBasis d t)
  | 0 => inferInstanceAs (Fintype d)
  | t + 1 => @instFintypeProd d (TensorBasis d t) inferInstance (repeatFintype d t)

instance repeatDecidableEq (d : Type) [DecidableEq d] : (t : ℕ) → DecidableEq (TensorBasis d t)
  | 0 => inferInstanceAs (DecidableEq d)
  | t + 1 => @instDecidableEqProd d (TensorBasis d t) inferInstance (repeatDecidableEq d t)

instance repeatNonempty (d : Type) [Nonempty d] : (t : ℕ) → Nonempty (TensorBasis d t)
  | 0 => inferInstanceAs (Nonempty d)
  | t + 1 => ⟨(Classical.choice (inferInstance : Nonempty d),
      Classical.choice (repeatNonempty d t))⟩

@[simp] theorem card_repeat (d : Type) [Fintype d] (t : ℕ) :
    Fintype.card (TensorBasis d t) = Fintype.card d ^ (t + 1) := by
  induction t with
  | zero => simp [TensorBasis, repeatFintype]
  | succ t ih =>
    change Fintype.card (d × TensorBasis d t) = _
    rw [Fintype.card_prod, ih, pow_succ]
    exact mul_comm _ _

variable {n d : Type} [Fintype n] [Fintype d] [DecidableEq n] [DecidableEq d]

/-- The actual t+1-fold tensor product channel. -/
def tensorPower (Φ : CPTPMap n d) : (t : ℕ) → CPTPMap (TensorBasis n t) (TensorBasis d t)
  | 0 => Φ
  | t + 1 => Φ ⊗ᶜᵖ tensorPower Φ t

/-- One-shot Holevo information per use for a positive tensor power. -/
def rate (Φ : CPTPMap n d) (t : ℕ) : ℝ :=
  holevo (tensorPower Φ t) / (t + 1 : ℕ)

/-- Classical capacity in its regularized Holevo form. -/
def regularizedHolevoCapacity (Φ : CPTPMap n d) : ℝ :=
  sSup (Set.range (rate Φ))

theorem rate_le_log_dimension [Nonempty n] (Φ : CPTPMap n d) (t : ℕ) :
    rate Φ t ≤ Real.log (Fintype.card d) := by
  have h := holevo_le_of_entropy_lower (tensorPower Φ t)
    (fun ρ ↦ Sᵥₙ_nonneg (tensorPower Φ t ρ))
  simp only [sub_zero, card_repeat, Nat.cast_pow, Real.log_pow] at h
  unfold rate
  apply (div_le_iff₀ (show 0 < ((t + 1 : ℕ) : ℝ) by positivity)).mpr
  simpa only [mul_comm] using h

theorem rate_bddAbove [Nonempty n] (Φ : CPTPMap n d) :
    BddAbove (Set.range (rate Φ)) := by
  refine ⟨Real.log (Fintype.card d), ?_⟩
  rintro x ⟨t, rfl⟩
  exact rate_le_log_dimension Φ t

/-- Using entanglement within pairs gives a classical rate at least half the
two-copy Holevo information. -/
theorem half_two_copy_le_capacity [Nonempty n] (Φ : CPTPMap n d) :
    holevo (Φ ⊗ᶜᵖ Φ) / 2 ≤ regularizedHolevoCapacity Φ := by
  change rate Φ 1 ≤ sSup (Set.range (rate Φ))
  exact le_csSup (rate_bddAbove Φ) (Set.mem_range_self 1)

theorem capacity_le_log_dimension [Nonempty n] (Φ : CPTPMap n d) :
    regularizedHolevoCapacity Φ ≤ Real.log (Fintype.card d) := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨t, rfl⟩
  exact rate_le_log_dimension Φ t

/-- The two inequalities in the main theorem imply an explicit capacity gap. -/
theorem capacity_gap_of_one_two_copy [Nonempty n] (Φ : CPTPMap n d)
    {N : ℝ} (hone : holevo Φ < 1 / N) (htwo : N < holevo (Φ ⊗ᶜᵖ Φ)) :
    N / 2 - 1 / N < regularizedHolevoCapacity Φ - holevo Φ := by
  have hcap := half_two_copy_le_capacity Φ
  linarith

/-- Choosing N = 2(max(B,0)+2) makes the resulting capacity gap larger than B. -/
theorem capacity_gap_exceeds [Nonempty n] (Φ : CPTPMap n d) (B : ℝ)
    (hone : holevo Φ < 1 / (2 * (max B 0 + 2)))
    (htwo : 2 * (max B 0 + 2) < holevo (Φ ⊗ᶜᵖ Φ)) :
    B < regularizedHolevoCapacity Φ - holevo Φ := by
  have hN : 1 ≤ 2 * (max B 0 + 2) := by nlinarith [le_max_right B 0]
  have hrec : 1 / (2 * (max B 0 + 2)) ≤ 1 :=
    (div_le_one (by linarith : 0 < 2 * (max B 0 + 2))).mpr hN
  have hgap := capacity_gap_of_one_two_copy Φ hone htwo
  nlinarith [le_max_left B 0]

end MainCapacity
