import MainTheorem
import MainCapacity

/-! The unbounded classical-capacity gap stated after the main theorem. -/
noncomputable section
set_option maxRecDepth 4096
open MainHolevo MainCapacity MainTheorem

namespace MainCapacityCorollary

/-- The same explicit channels have an explicitly diverging capacity gap. -/
theorem main_capacity_gap (N : ℝ) (hN : 1 ≤ N) :
    N / 2 - 1 / N <
      regularizedHolevoCapacity (channelFor N hN) - holevo (channelFor N hN) := by
  obtain ⟨hone, htwo⟩ := MainTheorem.main_theorem N hN
  exact capacity_gap_of_one_two_copy (channelFor N hN) hone htwo

/-- A target gain parameter large enough for any prescribed capacity gap. -/
def gainParameter (B : ℝ) : ℝ := 2 * (max B 0 + 2)

lemma gainParameter_ge_one (B : ℝ) : 1 ≤ gainParameter B := by
  unfold gainParameter
  nlinarith [le_max_right B 0]

/-- No finite constant bounds the gap between classical capacity and one-shot
Holevo information, already within the explicitly prescribed channel family. -/
theorem unbounded_capacity_gap (B : ℝ) :
    B < regularizedHolevoCapacity (channelFor (gainParameter B) (gainParameter_ge_one B)) -
      holevo (channelFor (gainParameter B) (gainParameter_ge_one B)) := by
  obtain ⟨hone, htwo⟩ := MainTheorem.main_theorem
    (gainParameter B) (gainParameter_ge_one B)
  exact capacity_gap_exceeds _ B hone htwo

end MainCapacityCorollary

#print axioms MainCapacityCorollary.unbounded_capacity_gap
