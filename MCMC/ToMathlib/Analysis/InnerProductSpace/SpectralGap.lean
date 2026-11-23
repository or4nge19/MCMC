/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import MCMC.ToMathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# The spectral gap of a positive compact operator with a simple top eigenvalue

Let `Q ≠ 0` be a positive compact operator on a complex Hilbert space, `Ω` a unit eigenvector of
`Q` for the eigenvalue `‖Q‖`, and suppose that every eigenvector of `Q` for `‖Q‖` lies in
`ℂ ∙ Ω`. With `Π` the orthogonal projection onto `ℂ ∙ Ω` and `R = Q / ‖Q‖ - Π`,

* `ContinuousLinearMap.norm_inv_norm_smul_sub_starProjection_lt_one`: `‖R‖ < 1`.

`R` is self-adjoint and compact with `R Ω = 0`, so its spectral radius is its norm, and every
nonzero spectral value `z` of `R` is an eigenvalue with a unit eigenvector `u ⊥ Ω`; then
`Q u = ‖Q‖ z • u`, so `0 ≤ z ≤ 1` by positivity and the operator norm, and `z = 1` would put `u`
in `ℂ ∙ Ω`.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Theorems VI.6 and VI.15.

Staged for `Mathlib/Analysis/InnerProductSpace/Positive.lean`. Searched on 2026-11-23: the pinned
Mathlib has no spectral-gap statement and no strict bound `< 1` for `Q / ‖Q‖ - Π`.
-/

public section

open scoped InnerProductSpace NNReal ENNReal ComplexOrder

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The spectral gap of a positive compact operator with a simple top eigenvalue.** If
`0 ≤ Q ≠ 0` is compact, `‖Ω‖ = 1`, `Q Ω = ‖Q‖ • Ω`, and every `v` with `Q v = ‖Q‖ • v` lies in
`ℂ ∙ Ω`, then `‖Q / ‖Q‖ - Π‖ < 1`, `Π` the orthogonal projection onto `ℂ ∙ Ω`. -/
theorem norm_inv_norm_smul_sub_starProjection_lt_one {Q : H →L[ℂ] H}
    (hQc : IsCompactOperator Q) (hQ : 0 ≤ Q) (hQ0 : Q ≠ 0) {Ω : H} (hΩ : ‖Ω‖ = 1)
    (hQΩ : Q Ω = (‖Q‖ : ℂ) • Ω) (hs : ∀ v, Q v = (‖Q‖ : ℂ) • v → v ∈ ℂ ∙ Ω) :
    ‖(‖Q‖ : ℂ)⁻¹ • Q - (ℂ ∙ Ω).starProjection‖ < 1 := by
  have hl : (‖Q‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hQ0)
  have hn : 0 < ‖Q‖ := norm_pos_iff.2 hQ0
  have hc : (0 : ℂ) ≤ (‖Q‖ : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact Complex.zero_le_real.2 (inv_nonneg.2 (norm_nonneg Q))
  have hQp := nonneg_iff_isPositive.1 hQ
  have hΩΩ : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]; simp
  have hPc : IsCompactOperator (ℂ ∙ Ω).starProjection := by
    have h : ⇑(ℂ ∙ Ω).starProjection = ⇑((innerSL ℂ Ω).smulRight Ω) := funext fun x ↦ by
      rw [Submodule.starProjection_unit_singleton ℂ hΩ, smulRight_apply, innerSL_apply_apply]
    rw [h]
    exact isCompactOperator_smulRight _ _
  have hQm : Q ∈ compactOperator (RingHom.id ℂ) H H := hQc
  have hPm : (ℂ ∙ Ω).starProjection ∈ compactOperator (RingHom.id ℂ) H H := hPc
  obtain ⟨R, hR⟩ : ∃ R : H →L[ℂ] H, R = (‖Q‖ : ℂ)⁻¹ • Q - (ℂ ∙ Ω).starProjection := ⟨_, rfl⟩
  rw [← hR]
  have hRsa : IsSelfAdjoint R := by
    rw [hR]
    exact ((IsSelfAdjoint.of_nonneg hc).smul hQp.isSelfAdjoint).sub
      (isSelfAdjoint_starProjection _)
  have hRm : R ∈ compactOperator (RingHom.id ℂ) H H := by
    rw [hR]
    exact (compactOperator (RingHom.id ℂ) H H).sub_mem
      ((compactOperator (RingHom.id ℂ) H H).smul_mem ((‖Q‖ : ℂ)⁻¹) hQm) hPm
  have hRc : IsCompactOperator R := hRm
  have hRΩ : R Ω = 0 := by
    rw [hR, sub_apply, smul_apply, hQΩ, smul_smul, inv_mul_cancel₀ hl, one_smul,
      Submodule.starProjection_unit_singleton ℂ hΩ, hΩΩ, one_smul, sub_self]
  have : Nontrivial (H →L[ℂ] H) := ⟨⟨Q, 0, hQ0⟩⟩
  suffices hsp : spectralRadius ℂ R < ((1 : ℝ≥0) : ℝ≥0∞) by
    rw [hRsa.spectralRadius_eq_nnnorm] at hsp
    exact (NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hsp)).trans_eq NNReal.coe_one
  refine spectrum.spectralRadius_lt_of_forall_lt R fun z hz ↦ ?_
  by_cases hz0 : z = 0
  · rw [hz0, nnnorm_zero]
    exact zero_lt_one
  obtain ⟨w, hw⟩ := ((hRc.hasEigenvalue_iff_mem_spectrum hz0).2 hz).exists_hasEigenvector
  have hRw : R w = z • w := hw.apply_eq_smul
  obtain ⟨u, hu1, hRu⟩ : ∃ u : H, ‖u‖ = 1 ∧ R u = z • u :=
    ⟨(‖w‖⁻¹ : ℂ) • w, norm_smul_inv_norm hw.2, by rw [map_smul, hRw, smul_comm]⟩
  have hzre : z = (z.re : ℂ) := hRsa.mem_spectrum_eq_re hz
  have huu : ⟪u, u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu1]; simp
  have hΩu : ⟪Ω, u⟫_ℂ = 0 := by
    have h1 : z * ⟪Ω, u⟫_ℂ = 0 := by
      rw [← inner_smul_right, ← hRu, ← hRsa.isSymmetric.apply_clm, hRΩ, inner_zero_left]
    exact (mul_eq_zero.1 h1).resolve_left hz0
  have hQu : Q u = ((‖Q‖ : ℂ) * z) • u := by
    have h := hRu
    rw [hR, sub_apply, smul_apply, Submodule.starProjection_unit_singleton ℂ hΩ, hΩu, zero_smul,
      sub_zero] at h
    rw [mul_smul, ← h, smul_smul, mul_inv_cancel₀ hl, one_smul]
  have ht0 : 0 ≤ z.re := by
    have h := hQp.inner_nonneg_right u
    rw [hQu, inner_smul_right, huu, mul_one, hzre, ← Complex.ofReal_mul] at h
    exact (mul_nonneg_iff_of_pos_left hn).1 (Complex.zero_le_real.1 h)
  have hz1 : ‖z‖ ≤ 1 := by
    have h := Q.le_opNorm u
    rw [hQu, norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg Q), hu1,
      mul_one, mul_one] at h
    exact le_of_mul_le_mul_left (h.trans_eq (mul_one _).symm) hn
  have hz1' : ‖z‖ ≠ 1 := by
    intro h1
    have hz : z = 1 := by
      rw [hzre] at h1 ⊢
      rw [Complex.norm_real, Real.norm_of_nonneg ht0] at h1
      rw [h1, Complex.ofReal_one]
    rw [hz, mul_one] at hQu
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hs u hQu)
    rw [← hc, inner_smul_right, hΩΩ, mul_one] at hΩu
    rw [← hc, hΩu, zero_smul, norm_zero] at hu1
    exact zero_ne_one hu1
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
  exact lt_of_le_of_ne hz1 hz1'

end ContinuousLinearMap
