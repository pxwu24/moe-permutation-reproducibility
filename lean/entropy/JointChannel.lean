import JointBound
import TensorBridge
import JointEntropy
import SingleEntropy

/-! The joint-copy lemma for the actual tensor product of a channel and its
entrywise conjugate, on the normalized maximally entangled input. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace InnerProductSpace ComplexOrder
open EntropyLemmas.BellAlgebra EntropyLemmas.TensorBridge

namespace SuppressorEntropy

variable {n k : ℕ}

/-- Entropy of the explicitly stated reference spectrum. -/
def referenceEntropy (k : ℕ) (γ ε : ℝ) : ℝ :=
  let s := γ^2 / (1+ε)^2
  Real.negMulLog ((1+s*((k:ℝ)-1))/(k:ℝ)^2) +
    ((k:ℝ)-1)*Real.negMulLog ((1-s)/(k:ℝ)^2) +
    ((k:ℝ)*((k:ℝ)-1))*Real.negMulLog (1/(k:ℝ)^2)

/-- The full joint-copy lemma. `hΦ` specifies the channel entries and `hconj`
specifies its ordinary entrywise conjugate on all matrices. No Bell-overlap,
pinching, majorization or entropy bound is assumed. -/
theorem joint_copy_lemma
    (hn : 0 < n) (hk : 2 ≤ k)
    (F H : Matrix (Fin n) (Fin n) ℂ) (hF : F.PosSemidef) (hHerm : H.IsHermitian)
    (U : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i, (U i).conjTranspose * U i = 1)
    (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hH : H * H = (γ : ℂ) • (1 + F)⁻¹)
    (htrace : F.trace.re ≤ n * ε)
    (Φ Φbar : CPTPMap (Fin n) (Fin k))
    (hΦ : ∀ X i j, Φ.map X i j = channelEntry (suppressorK H U) X i j)
    (hconj : ∀ X, Φbar.map X =
      (Φ.map (X.map (starRingEnd ℂ))).map (starRingEnd ℂ)) :
    minimumOutputEntropy (Φ.prod Φbar) ≤ referenceEntropy k γ ε := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hk0 : 0 < k := by omega
  have : Nonempty (Fin k) := ⟨⟨0, hk0⟩⟩
  let σ := (Φ.prod Φbar) (MState.pure (Ket.MES (Fin n)))
  let P := diagonalTensorProjection k
  let E := bellProjection k
  let s := γ^2/(1+ε)^2
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs1 : s < 1 := by
    apply (div_lt_one (by positivity : 0 < (1+ε)^2)).mpr
    nlinarith
  have hbar := conjugate_matrix_unit_entries Φ Φbar (suppressorK H U) hΦ hconj
  have hsym := suppressorK_conjTranspose H U hHerm.eq
  have hdiag := product_bell_diagonal Φ Φbar (suppressorK H U) hΦ hbar hsym
    (suppressorK_diagonal H U hU) hn.ne'
  have hmass : ⟪σ.M,P⟫_ℝ = 1/(k:ℝ) :=
    inner_diagonalTensorProjection_of_uniform σ hk0.ne' hdiag
  have hq : (1+s*((k:ℝ)-1))/(k:ℝ)^2 ≤ ⟪σ.M,E⟫_ℝ := by
    rw [show ⟪σ.M,E⟫_ℝ = (bellOverlap (suppressorK H U)).re from
      product_bell_inner Φ Φbar (suppressorK H U) hΦ hbar hsym]
    exact suppressor_bellOverlap_lower hn hk0 F H hF hHerm U hU γ ε
      hγ0.le hε.le hH htrace
  have hentropy := entropy_le_bell_projections σ P E
    (diagonalTensorProjection_idempotent k) (bellProjection_idempotent k)
    (diagonalTensorProjection_mul_bellProjection k)
    (bellProjection_mul_diagonalTensorProjection k)
    k hk (by simp [pow_two]) (diagonalTensorProjection_trace k)
    (bellProjection_trace k) s hs0 hs1 hmass hq
  exact (minimumOutputEntropy_le (Φ.prod Φbar)
    (MState.pure (Ket.MES (Fin n)))).trans hentropy

#print axioms joint_copy_lemma

end SuppressorEntropy
