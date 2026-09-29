import AdderTrace

/-!
# The adder statements in the Supplement

This module matches Lemmas 5 and 6 and Proposition 4 of the current paper.
Lemma 5 is stated for every word of length at most `4*L`, including odd
lengths, and branches on the actual finite permutation matrix being the
identity. No padding argument or abstract nonidentity assumption is used.

`MatrixGrid.energy W` is the squared unnormalized Hilbert--Schmidt norm.
For Hermitian W it equals the real trace of W^2; the trace of the even
moment is real as well. The use of `.re` is solely to express an ordered
inequality in Lean's real numbers.
-/

open scoped BigOperators

namespace SupplementAdder

open AdderTrace

/-- The old growth proof also applies when the instruction list has any
length at most 4L, without requiring the list to have even length. -/
lemma cyclic_conjugation_entry_bound_of_length_le (M L : ℕ) (hM : 2 ≤ M)
    (xs : List (ℤ × ℤ)) (hlen : xs.length ≤ 4*L)
    (hx : ∀ x ∈ xs, |x.2| = 1 ∧ 0 ≤ x.1 ∧ x.1 ≤ (M:ℤ)-1)
    (i j : Fin 2) :
    ((shearA (-firstIndex xs 0) * conjugateWord xs * shearA (firstIndex xs 0)-1) i j).natAbs
      ≤ wordBound M L := by
  have h := rowBound_sub_one_entry (cyclic_conjugation_rowBound M hM xs hx) i j
  have hM' : (2 : ℤ) ≤ M := by exact_mod_cast hM
  have hp : (4*(M:ℤ)-1)^xs.length ≤ (4*(M:ℤ)-1)^(4*L) :=
    pow_le_pow_right₀ (by omega) hlen
  have hsub : (1 : ℕ) ≤ 4*M := by omega
  have hcast : ((4*M-1 : ℕ) : ℤ) = 4*(M : ℤ)-1 := by
    rw [Nat.cast_sub hsub]
    norm_num
  have h' : |((shearA (-firstIndex xs 0) * conjugateWord xs * shearA (firstIndex xs 0)-1) i j)| ≤
      ((wordBound M L : ℕ) : ℤ) := by
    simpa only [wordBound, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hcast] using
      h.trans (add_le_add_right hp 1)
  rw [← Int.natCast_natAbs] at h'
  exact_mod_cast h'

lemma nonidentity_word_fixed_card_le_of_length_le (Q M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (xs : List (ℤ × ℤ)) (hlen : xs.length ≤ 4*L)
    (hx : ∀ x ∈ xs, |x.2| = 1 ∧ 0 ≤ x.1 ∧ x.1 ≤ (M:ℤ)-1)
    (hne : conjugateWord xs ≠ 1) :
    Fintype.card {x : ZMod Q × ZMod Q // labelAction Q (conjugateWord xs) x = x}
      ≤ Q * wordBound M L := by
  classical
  let H := shearA (-firstIndex xs 0)*conjugateWord xs*shearA (firstIndex xs 0)
  have hH : H ≠ 1 := shear_conjugate_ne_one _ hne _
  have hb (i j : Fin 2) : ((H-1) i j).natAbs ≤ wordBound M L :=
    cyclic_conjugation_entry_bound_of_length_le M L hM xs hlen hx i j
  have hcard := matrix_fixed_card_le Q (wordBound M L)
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

/-- The permutation matrix T_w^epsilon of equation (S32). -/
noncomputable def supplementWordMatrix (Q : ℕ) [NeZero Q]
    (word : List AdderCones.Syllable) :
    Matrix (ZMod Q × ZMod Q) (ZMod Q × ZMod Q) ℂ :=
  permutationMatrix (modularRepresentation Q (AdderCones.freeWord word))

/-- This definition is the actual ordered product of the powers of T_i. -/
lemma supplementWordMatrix_eq_product (Q : ℕ) [NeZero Q]
    (word : List AdderCones.Syllable) :
    supplementWordMatrix Q word =
      permutationMatrix ((word.map fun p => (modularStepPerm Q p.1 1)^p.2).prod) := by
  unfold supplementWordMatrix AdderCones.freeWord
  simp only [map_list_prod, List.map_map, Function.comp_def, map_zpow, modularRepresentation_of]

/-- Lemma 5, equation (S33), with exactly its two alternatives. The extra
size condition Q>B_L is not needed for this lemma. -/
theorem lemma5_word_trace (Q M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (_hL : 1 ≤ L) (word : List AdderCones.Syllable)
    (_hne : 1 ≤ word.length) (hlen : word.length ≤ 4*L)
    (hletters : ∀ p ∈ word, |p.2| = 1 ∧ p.1 < M) :
    (supplementWordMatrix Q word = 1 →
      (Matrix.trace (supplementWordMatrix Q word)).re / (Q:ℝ)^2 = 1) ∧
    (supplementWordMatrix Q word ≠ 1 →
      (Matrix.trace (supplementWordMatrix Q word)).re / (Q:ℝ)^2 ≤
        (wordBound M L : ℝ) / Q) := by
  classical
  have hQ : (0:ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  constructor
  · intro h
    rw [h]
    simp [Matrix.trace_one, Fintype.card_prod, ZMod.card, pow_two, ne_of_gt hQ]
  · intro hne
    have hi : conjugateWord (liftWord word) ≠ 1 := by
      intro h
      have hp : modularRepresentation Q (AdderCones.freeWord word) = 1 := by
        apply Equiv.ext
        intro x
        rw [modularRepresentation_freeWord_apply, h, labelAction_one]
        rfl
      apply hne
      simp [supplementWordMatrix, hp]
    have hc := nonidentity_word_fixed_card_le_of_length_le Q M L hM (liftWord word)
      (by simpa [liftWord] using hlen)
      (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        have hpi : (p.1:ℤ) < M := by exact_mod_cast (hletters p hp).2
        exact ⟨(hletters p hp).1, by omega, by omega⟩) hi
    have hcount : (Fintype.card {x : ZMod Q × ZMod Q //
        modularRepresentation Q (AdderCones.freeWord word) x = x} : ℝ) ≤
        (Q:ℝ) * wordBound M L := by
      simpa only [modularRepresentation_freeWord_apply, Nat.cast_mul] using
        (show (Fintype.card {x : ZMod Q × ZMod Q //
          labelAction Q (conjugateWord (liftWord word)) x = x} : ℝ) ≤
          ((Q * wordBound M L : ℕ):ℝ) from by exact_mod_cast hc)
    rw [supplementWordMatrix, trace_permutationMatrix]
    simp only [Complex.natCast_re]
    apply (div_le_iff₀ (sq_pos_of_pos hQ)).2
    calc
      _ ≤ (Q:ℝ) * wordBound M L := hcount
      _ = (wordBound M L : ℝ)/(Q:ℝ)*(Q:ℝ)^2 := by field_simp

/-- Identifies the coefficient sum with the paper's squared Hilbert--Schmidt norm. -/
lemma energy_eq_hilbertSchmidt_trace {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ) :
    MatrixGrid.energy W = (Matrix.trace (W.conjTranspose * W)).re := by
  simp only [MatrixGrid.energy, Fintype.sum_prod_type, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change Complex.normSq (W i j) = (star (W i j) * W i j).re
  rw [mul_comm]
  simp [Complex.mul_conj]

/-- Lemma 6, equation (S35), with its common Hilbert--Schmidt factor
and the exponent L on k(k-1). The original parameter restrictions are
retained although the already verified raw bound is stronger. -/
theorem lemma6_moment_bound (Q r M L : ℕ) [NeZero Q]
    (hM : 2 ≤ M) (_hr : 1 ≤ r) (_hL : 1 ≤ L) (_hQ : wordBound M L < Q)
    (W : Matrix (Fin (M^r)) (Fin (M^r)) ℂ)
    (hD : ∀ i, W i i = 0) (hH : ∀ i j, W j i = star (W i j)) :
    (Matrix.trace (momentMatrix (finAdderMatrix Q r M) W ^ (2*L))).re /
        (Q:ℝ)^(2*r) ≤
      ((delta M r)^(2*L) + (wordBound M L : ℝ)/Q *
        ((M^r * (M^r-1) : ℕ):ℝ)^L) *
        (Real.sqrt (Matrix.trace (W.conjTranspose * W)).re)^(2*L) := by
  let k := M^r
  let E := MatrixGrid.energy W
  let D := delta M r
  let B := (wordBound M L : ℝ)/(Q:ℝ)
  have hB : 0 ≤ B := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hK : 0 ≤ ((k*(k-1):ℕ):ℝ) := Nat.cast_nonneg _
  have hraw := finite_adder_raw_moment_bound Q r M L hM W hD hH
  rw [← MatrixGrid.energy_eq_trace_sq W hH] at hraw
  have hl1 : offDiagL1 W ≤ Real.sqrt ((k*(k-1):ℕ):ℝ) * Real.sqrt E := by
    have h := coefficient_l1_le_offDiag_energy W hD
    rw [sum_coefficients_eq_offDiag W hD (fun z => ‖z‖) (by simp)] at h
    exact h
  have hl1nonneg : 0 ≤ offDiagL1 W := by
    unfold offDiagL1
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hl1nonneg hl1 (2*L)) hB
  have hsqrt : (Real.sqrt ((k*(k-1):ℕ):ℝ))^(2*L) = ((k*(k-1):ℕ):ℝ)^L := by
    rw [pow_mul, Real.sq_sqrt hK]
  have hresult : normalizedTrace (momentMatrix (finAdderMatrix Q r M) W ^ (2*L)) ≤
      (D^(2*L) + B * ((k*(k-1):ℕ):ℝ)^L) * (Real.sqrt E)^(2*L) := by
    calc
      _ ≤ (D * Real.sqrt E)^(2*L) + B * offDiagL1 W^(2*L) := hraw
      _ ≤ (D * Real.sqrt E)^(2*L) +
          B * (Real.sqrt ((k*(k-1):ℕ):ℝ) * Real.sqrt E)^(2*L) :=
        add_le_add_left hp _
      _ = _ := by rw [mul_pow, mul_pow, hsqrt]; ring
  simpa only [normalizedTrace, tensorLabel_card, Nat.cast_pow, D, B, E, k,
    energy_eq_hilbertSchmidt_trace] using hresult

/-- Proposition 4, equation (S31), is the original checked final theorem. -/
alias proposition4_trace_bound := technical_trace_bound

#print axioms lemma5_word_trace
#print axioms lemma6_moment_bound
#print axioms proposition4_trace_bound

end SupplementAdder
