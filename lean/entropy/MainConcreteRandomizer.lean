import MainPauli
import MainParameters

/-! The explicit power-of-two field and the randomizer with the parameters of
the main theorem. -/

noncomputable section
open scoped BigOperators

namespace MainConcreteRandomizer
open MainParameters MainPauli

abbrev SeedField (r : ℕ) := GaloisField 2 (randomizerT r)

instance (r : ℕ) : Fintype (SeedField r) := Fintype.ofFinite _
instance (r : ℕ) : DecidableEq (SeedField r) := Classical.decEq _

theorem card_seedField (r : ℕ) (hr : 0 < r) :
    Fintype.card (SeedField r) = randomizerH r := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 (randomizerT r) (randomizerT_pos r hr).ne'

def seeds (r : ℕ) : SeedField r × SeedField r → Bits (27 * r) × Bits (27 * r) :=
  fieldSeed (SeedField r) (27 * r)

theorem card_seeds (r : ℕ) (hr : 0 < r) :
    Fintype.card (SeedField r × SeedField r) = randomizerSize r := by
  simp only [Fintype.card_prod, card_seedField r hr, randomizerSize, pow_two]

theorem card_output (r : ℕ) : Fintype.card (Bits (27 * r)) = M ^ r := by
  simp [Bits, M, pow_mul]

theorem seed_count_bound (r : ℕ) (hr : 0 < r) :
    (Fintype.card (SeedField r × SeedField r) : ℝ) <
      108 ^ 2 * (r : ℝ) ^ 4 * a r := by
  rw [card_seeds r hr]
  exact randomizerSize_bound r hr

/-- The concrete randomizer, including the actual finite field and all seed
matrices, has the claimed Hilbert--Schmidt contraction. -/
theorem contraction (r : ℕ) (hr : 0 < r)
    (A : Matrix (Bits (27 * r)) (Bits (27 * r)) ℂ) (hA : Matrix.trace A = 0) :
    ‖vectorize (MainPauli.average (seeds r) A)‖ ^ 2 ≤
      ‖vectorize A‖ ^ 2 / ((r : ℝ) ^ 2 * a r) := by
  have h := fieldSeed_contraction (SeedField r) A hA
  have hc : (((27 * r + 27 * r - 1 : ℕ) : ℝ) /
      Fintype.card (SeedField r)) =
      (54 * (r : ℝ) - 1) / randomizerH r := by
    rw [card_seedField r hr, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hc] at h
  have hcoef := (randomizer_contraction_bound r hr).le
  have hnonneg : 0 ≤ (54 * (r : ℝ) - 1) / randomizerH r := by
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    apply div_nonneg _ (by positivity)
    linarith
  have hsq := pow_le_pow_left₀ hnonneg hcoef 2
  have hsqrt : (Real.sqrt (a r)) ^ 2 = a r := Real.sq_sqrt (a_pos r).le
  have heq : (1 / ((r : ℝ) * Real.sqrt (a r))) ^ 2 =
      1 / ((r : ℝ) ^ 2 * a r) := by
    rw [div_pow, mul_pow, hsqrt, one_pow]
  change ‖vectorize (MainPauli.average (fieldSeed (SeedField r) (27 * r)) A)‖ ^ 2 ≤ _
  calc
    _ ≤ _ := h
    _ ≤ (1 / ((r : ℝ) * Real.sqrt (a r))) ^ 2 * ‖vectorize A‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = _ := by rw [heq]; ring

end MainConcreteRandomizer
