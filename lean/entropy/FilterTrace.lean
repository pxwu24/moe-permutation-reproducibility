import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# A. Trace estimate for the suppressor

The AM--GM proof below is adapted from `QICLean.Analysis.MatrixTraceInequalities`
and `QICLean.Analysis.DeterminantTraceBound`, copyright 2026 TNLean contributors,
Apache 2.0, commit `cdaa636d1f41560f7caca7077c11068229cb9727`.
The suppressor estimate is proved here by determinant algebra, without matrix logarithms.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix Finset

namespace Suppressor

lemma amgm_pow {D : ℕ} (f : Fin D → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (D : ℝ) ^ D * ∏ i, f i ≤ (∑ i, f i) ^ D := by
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · subst hD0; simp
  have hD0' : D ≠ 0 := hDpos.ne'
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD0'
  have hDR_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hP0 : 0 ≤ ∏ i, f i := Finset.prod_nonneg fun i _ => hf i
  have hDpow_pos : (0 : ℝ) < (D : ℝ) ^ D := pow_pos hDR_pos D
  have hwsum : ∑ _i : Fin D, (D : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hDR]
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin D => (D : ℝ)⁻¹) f (fun i _ => by positivity) hwsum (fun i _ => hf i)
  rw [Real.finsetProd_rpow Finset.univ f (fun i _ => hf i) ((D : ℝ)⁻¹),
    ← Finset.mul_sum] at hamgm
  have hraise := pow_le_pow_left₀ (Real.rpow_nonneg hP0 _) hamgm D
  rw [Real.rpow_inv_natCast_pow hP0 hD0', mul_pow, inv_pow] at hraise
  calc (D : ℝ) ^ D * ∏ i, f i
      ≤ (D : ℝ) ^ D * (((D : ℝ) ^ D)⁻¹ * (∑ i, f i) ^ D) :=
        mul_le_mul_of_nonneg_left hraise hDpow_pos.le
    _ = (∑ i, f i) ^ D := mul_inv_cancel_left₀ hDpow_pos.ne' _

lemma psd_det_amgm {D : ℕ} {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosSemidef) :
    (D : ℝ) ^ D * A.det.re ≤ A.trace.re ^ D := by
  have hdet : A.det.re = ∏ i, hA.1.eigenvalues i := by
    simp only [hA.1.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    exact RCLike.ofReal_re (K := ℂ) _
  have htr : A.trace.re = ∑ i, hA.1.eigenvalues i := by
    simp only [hA.1.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
    exact RCLike.ofReal_re (K := ℂ) _
  rw [hdet, htr]
  exact amgm_pow hA.1.eigenvalues fun i => hA.eigenvalues_nonneg i

lemma gram_det_amgm {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) :
    (D : ℝ) ^ D * ‖A.det‖ ^ 2 ≤ (Aᴴ * A).trace.re ^ D := by
  have hpsd : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hdet : (Aᴴ * A).det.re = ‖A.det‖ ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose,
      show star A.det * A.det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) by
        simpa using RCLike.conj_mul (K := ℂ) A.det,
      Complex.ofReal_re]
  simpa only [hdet] using psd_det_amgm hpsd

lemma psd_det_norm_eq_re {D : ℕ} {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosSemidef) : ‖A.det‖ = A.det.re := by
  have hdet : (‖A.det‖ : ℂ) = A.det := RCLike.norm_of_nonneg' hA.det_nonneg
  simpa only [Complex.ofReal_re] using congrArg Complex.re hdet

lemma psd_det_le_trace_bound {D : ℕ} (hD : 0 < D)
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef) {b : ℝ}
    (htr : A.trace.re ≤ D * b) : ‖A.det‖ ≤ b ^ D := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have htrace : 0 ≤ A.trace.re := by
    rw [hA.1.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => by simpa using hA.eigenvalues_nonneg i
  have hp := (psd_det_amgm hA).trans (pow_le_pow_left₀ htrace htr D)
  rw [mul_pow, ← psd_det_norm_eq_re hA] at hp
  exact (mul_le_mul_iff_right₀ (pow_pos hDR D)).mp hp

lemma determinant_scalar_bound {D : ℕ} (hD : 0 < D)
    {a b p γ e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hγ : 0 ≤ γ) (he : 0 < e)
    (hgram : (D : ℝ) ^ D * a ^ 2 ≤ p ^ D)
    (hdet : b ≤ e ^ D) (hprod : a * b = γ ^ D) :
    γ ^ 2 / e ^ 2 ≤ p / D := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hb2 : b ^ 2 ≤ (e ^ D) ^ 2 := pow_le_pow_left₀ hb hdet 2
  have hmul := mul_le_mul hgram hb2 (sq_nonneg b) (pow_nonneg hp D)
  have hleft : ((D : ℝ) * γ ^ 2) ^ D = ((D : ℝ) ^ D * a ^ 2) * b ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm 2 D, pow_mul, ← hprod, mul_pow]
    ring
  have hright : p ^ D * (e ^ D) ^ 2 = (p * e ^ 2) ^ D := by
    rw [mul_pow, ← pow_mul, mul_comm D 2, pow_mul]
  rw [← hleft, hright] at hmul
  have hbase : (D : ℝ) * γ ^ 2 ≤ p * e ^ 2 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) hD.ne').mp hmul
  apply (div_le_div_iff₀ (sq_pos_of_pos he) hDR).mpr
  nlinarith

lemma unitary_det_norm {D : ℕ} {V : Matrix (Fin D) (Fin D) ℂ}
    (hV : Vᴴ * V = 1) : ‖V.det‖ = 1 := by
  have hdet : star V.det * V.det = (1 : ℂ) := by
    simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] using
      congrArg Matrix.det hV
  have hsq := congrArg norm hdet
  simp only [norm_mul, norm_star, norm_one] at hsq
  nlinarith [norm_nonneg V.det]

/-- The filter determinant cancels the determinant of `I + F`. -/
lemma filter_determinant_identity {D : ℕ} {F H V : Matrix (Fin D) (Fin D) ℂ}
    (hF : F.PosSemidef) {γ : ℝ} (hγ : 0 ≤ γ)
    (hH : H * H = (γ : ℂ) • (1 + F)⁻¹) (hV : Vᴴ * V = 1) :
    ‖(H * V * H).det‖ * ‖(1 + F).det‖ = γ ^ D := by
  have hB : (1 + F).PosDef := Matrix.PosDef.one.add_posSemidef hF
  have hBinv : IsUnit (1 + F).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit
  have hcancel : H * H * (1 + F) = (γ : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [hH, Matrix.smul_mul, Matrix.nonsing_inv_mul _ hBinv]
  have hnorm := congrArg (fun A : Matrix (Fin D) (Fin D) ℂ => ‖A.det‖) hcancel
  simp only [Matrix.det_mul, norm_mul, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hγ] at hnorm
  simpa only [Matrix.det_mul, norm_mul, unitary_det_norm hV, mul_one] using hnorm

/-- A trace bound for `F` controls every filtered unitary Hilbert--Schmidt norm. -/
lemma filter_trace_lower_bound {D : ℕ} (hD : 0 < D)
    {F H V : Matrix (Fin D) (Fin D) ℂ} (hF : F.PosSemidef)
    {γ ε : ℝ} (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hH : H * H = (γ : ℂ) • (1 + F)⁻¹) (hV : Vᴴ * V = 1)
    (htrace : F.trace.re ≤ D * ε) :
    γ ^ 2 / (1 + ε) ^ 2 ≤ ((H * V * H)ᴴ * (H * V * H)).trace.re / D := by
  let A := H * V * H
  have hB : (1 + F).PosSemidef := Matrix.PosSemidef.one.add hF
  have htrB : (1 + F).trace.re ≤ D * (1 + ε) := by
    simp only [Matrix.trace_add, Matrix.trace_one, Complex.add_re,
      Complex.natCast_re, Fintype.card_fin]
    nlinarith
  have htrA : 0 ≤ (Aᴴ * A).trace.re := by
    have hpsd := Matrix.posSemidef_conjTranspose_mul_self A
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => by simpa using hpsd.eigenvalues_nonneg i
  exact determinant_scalar_bound hD (norm_nonneg _) (norm_nonneg _) htrA hγ
    (by positivity) (gram_det_amgm A) (psd_det_le_trace_bound hD hB htrB)
    (filter_determinant_identity hF hγ hH hV)

/-- Cyclicity expresses the preceding Gram trace in terms of `T = H²`. -/
lemma filtered_gram_trace {D : ℕ} {H V : Matrix (Fin D) (Fin D) ℂ}
    (hH : H.IsHermitian) :
    ((H * V * H)ᴴ * (H * V * H)).trace =
      (H * H * V * (H * H) * Vᴴ).trace := by
  calc
    ((H * V * H)ᴴ * (H * V * H)).trace =
        ((H * V * H) * (H * V * H)ᴴ).trace := Matrix.trace_mul_comm _ _
    _ = ((H * V * (H * H) * Vᴴ) * H).trace := by
      simp only [Matrix.conjTranspose_mul, hH.eq, Matrix.mul_assoc]
    _ = (H * (H * V * (H * H) * Vᴴ)).trace := Matrix.trace_mul_comm _ _
    _ = (H * H * V * (H * H) * Vᴴ).trace := by
      simp only [Matrix.mul_assoc]

/-- The normalized trace bound used for the Bell overlap. -/
lemma filter_trace_lower_bound_cyclic {D : ℕ} (hD : 0 < D)
    {F H V : Matrix (Fin D) (Fin D) ℂ} (hF : F.PosSemidef)
    (hHerm : H.IsHermitian) {γ ε : ℝ} (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hH : H * H = (γ : ℂ) • (1 + F)⁻¹) (hV : Vᴴ * V = 1)
    (htrace : F.trace.re ≤ D * ε) :
    γ ^ 2 / (1 + ε) ^ 2 ≤ (H * H * V * (H * H) * Vᴴ).trace.re / D := by
  rw [← filtered_gram_trace hHerm]
  exact filter_trace_lower_bound hD hF hγ hε hH hV htrace

end Suppressor
