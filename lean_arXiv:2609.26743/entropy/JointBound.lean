import FilterTrace
import BellAlgebra

/-! Bell-overlap lower bound from the suppressor trace hypothesis. -/

noncomputable section
open scoped BigOperators ComplexOrder
open EntropyLemmas.BellAlgebra

namespace SuppressorEntropy

variable {n k : ℕ}

lemma unitary_pair (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1) (i j : Fin k) :
    ((U i).conjTranspose * U j).conjTranspose *
      ((U i).conjTranspose * U j) = 1 := by
  have hi : U i * (U i).conjTranspose = 1 := mul_eq_one_comm.mp (hU i)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (U j).conjTranspose * (U i * (U i).conjTranspose) * U j := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hi, mul_one, hU j]

/-- The trace bound alone implies the required Bell-overlap lower bound. -/
theorem suppressor_bellOverlap_lower
    (hn : 0 < n) (hk : 0 < k)
    (F H : Matrix (Fin n) (Fin n) ℂ) (hF : F.PosSemidef) (hHerm : H.IsHermitian)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (γ ε : ℝ) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hH : H * H = (γ : ℂ) • (1 + F)⁻¹)
    (htrace : F.trace.re ≤ n * ε) :
    (1 + (γ^2 / (1+ε)^2) * ((k:ℝ)-1)) / (k:ℝ)^2 ≤
      (bellOverlap (suppressorK H U)).re := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  let s : ℝ := γ^2 / (1+ε)^2
  let t : Fin k → Fin k → ℝ := fun i j =>
    (Matrix.trace ((H * H) * ((U i).conjTranspose * U j) *
      (H * H) * ((U j).conjTranspose * U i))).re
  have ht (i j : Fin k) : (n:ℝ)*s ≤ t i j := by
    have h := Suppressor.filter_trace_lower_bound_cyclic hn hF hHerm hγ hε hH
      (unitary_pair U hU i j) htrace
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
    exact (mul_comm _ _).le.trans ((le_div_iff₀ hnR).mp h)
  have hsum : (k:ℝ)*((k:ℝ)-1)*((n:ℝ)*s) ≤
      ∑ i : Fin k, ∑ j ∈ Finset.univ.erase i, t i j := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      Finset.sum_le_sum (s := Finset.univ.erase i) fun j _ => ht i j
    simpa only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk.ne'), Nat.cast_one, mul_assoc] using h
  have heq : (bellOverlap (suppressorK H U)).re = 1/(k:ℝ)^2 +
      (∑ i : Fin k, ∑ j ∈ Finset.univ.erase i, t i j) / ((n:ℝ)*(k:ℝ)^3) := by
    rw [suppressor_bellOverlap H U hU hn.ne' hk.ne']
    simp only [offDiagonalSum, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.add_re, Complex.div_ofReal_re,
      Complex.one_re, Complex.re_sum, t]
  rw [heq]
  have hdiv := div_le_div_of_nonneg_right hsum (by positivity : 0 ≤ (n:ℝ)*(k:ℝ)^3)
  have halg : (1+s*((k:ℝ)-1))/(k:ℝ)^2 = 1/(k:ℝ)^2 +
      ((k:ℝ)*((k:ℝ)-1)*((n:ℝ)*s))/((n:ℝ)*(k:ℝ)^3) := by
    field_simp [hnR.ne', hkR.ne']
  change (1+s*((k:ℝ)-1))/(k:ℝ)^2 ≤ _
  rw [halg]
  linarith


#print axioms suppressor_bellOverlap_lower

end SuppressorEntropy
