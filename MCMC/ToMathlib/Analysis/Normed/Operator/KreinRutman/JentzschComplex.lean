/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import MCMC.ToMathlib.Analysis.Normed.Operator.KreinRutman.Jentzsch
public import MCMC.ToMathlib.MeasureTheory.Function.LpRealForm

/-!
# Jentzsch's theorem on the complex `L²` of a finite measure

Let `μ` be a finite nonzero measure and `Q` a compact operator on the complex `L²(μ)` with a real
kernel bounded between two constants, `0 < c₁ ≤ κ ≤ c₂`:
`(Q g)(x) = ∫ κ(x, y) g(y) dμ(y)` for `μ`-almost every `x`. Let `T f = Re (Q f)` be its real form
on the real `L²(μ)` and `r = gelfandRadius T`. Jentzsch's theorem for `T`
(`IsCompactOperator.exists_gelfandRadius_sub_smul_smulRight_lt_of_pos_kernel`) passes to `Q`
through `Re (Q v) = T (Re v)` and `Im (Q v) = T (Im v)`
(`MeasureTheory.Lp.reCLM_compLpL_apply_eq_of_real_kernel`):

* `IsCompactOperator.exists_apply_eq_gelfandRadius_smul_of_pos_real_kernel`: `r > 0`; `r` is an
  eigenvalue of `Q` with an eigenvector `x₀ ≥ a • 1`, `a > 0`, real; every eigenvector of `Q` for
  `r` is a multiple of any nonzero one (the eigenvalue `r` is geometrically simple); and every
  real eigenvalue `t` of `Q` has `|t| ≤ r`.

## References

* R. Jentzsch, *Über Integralgleichungen mit positivem Kern*, J. reine angew. Math. 141 (1912).
* M. A. Krasnosel'skii, *Positive solutions of operator equations*, Noordhoff, 1964, §2.

Staged for `Mathlib/Analysis/Normed/Operator/KreinRutman.lean`.
-/

public section

open MeasureTheory

section JentzschComplex

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ]
  {Q : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} {T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {κ : X × X → ℝ} {c₁ c₂ : ℝ}

/-- **Jentzsch's theorem on the complex `L²(μ)`.** Let `Q` be compact with a real kernel,
`(Q g)(x) = ∫ κ(x, y) g(y) dμ(y)` almost everywhere, every section `κ(x, ·)` almost everywhere
strongly measurable, `0 < c₁ ≤ κ ≤ c₂`, and let `T f = Re (Q f)` be the real form of `Q`. Then
`r = gelfandRadius T > 0`; `Q (ι x₀) = r • ι x₀` for a real `x₀ ≥ a • 1`, `a > 0`, with
`ι x₀ ≠ 0`; for every `Ω ≠ 0` with `Q Ω = r • Ω`, every `v` with `Q v = r • v` lies in `ℂ ∙ Ω`;
and `|t| ≤ r` for every real eigenvalue `t` of `Q`. -/
theorem IsCompactOperator.exists_apply_eq_gelfandRadius_smul_of_pos_real_kernel
    (hQc : IsCompactOperator Q)
    (hT : ∀ f, T f = Complex.reCLM.compLpL 2 μ (Q (Complex.ofRealCLM.compLpL 2 μ f)))
    (hQ : ∀ g : Lp ℂ 2 μ, (Q g : X → ℂ) =ᵐ[μ] fun x ↦ ∫ y, (κ (x, y) : ℂ) * g y ∂μ)
    (hκm : ∀ x, AEStronglyMeasurable (fun y ↦ κ (x, y)) μ) (hc₁ : 0 < c₁)
    (hκ₁ : ∀ p, c₁ ≤ κ p) (hκ₂ : ∀ p, κ p ≤ c₂) :
    0 < gelfandRadius T ∧
      (∃ x₀ : Lp ℝ 2 μ, (∃ a : ℝ, 0 < a ∧ a • Lp.const 2 μ (1 : ℝ) ≤ x₀) ∧
        Complex.ofRealCLM.compLpL 2 μ x₀ ≠ 0 ∧
        Q (Complex.ofRealCLM.compLpL 2 μ x₀) =
          (gelfandRadius T : ℂ) • Complex.ofRealCLM.compLpL 2 μ x₀) ∧
      (∀ Ω : Lp ℂ 2 μ, Ω ≠ 0 → Q Ω = (gelfandRadius T : ℂ) • Ω →
        ∀ v, Q v = (gelfandRadius T : ℂ) • v → v ∈ ℂ ∙ Ω) ∧
      ∀ (t : ℝ) (v : Lp ℂ 2 μ), v ≠ 0 → Q v = (t : ℂ) • v → |t| ≤ gelfandRadius T := by
  have hTc : IsCompactOperator T := by
    rw [show (T : Lp ℝ 2 μ → Lp ℝ 2 μ) = _ from funext hT]
    exact (hQc.comp_clm (Complex.ofRealCLM.compLpL 2 μ)).clm_comp (Complex.reCLM.compLpL 2 μ)
  have hk : ∀ f : Lp ℝ 2 μ, (T f : X → ℝ) =ᵐ[μ] fun x ↦ ∫ y, κ (x, y) * f y ∂μ := fun f ↦ by
    rw [hT f]
    exact Lp.reCLM_compLpL_apply_ofRealCLM_compLpL_ae_eq_integral hQ f
  obtain ⟨hr, x₀, -, a, ha, hax₀, ℓ, hTx₀, hℓT, hℓx₀, -, hgap⟩ :=
    hTc.exists_gelfandRadius_sub_smul_smulRight_lt_of_pos_kernel hk hκm hc₁ hκ₁ hκ₂
  have hbd : ∀ (t : ℝ) (f : Lp ℝ 2 μ), f ≠ 0 → T f = t • f → |t| ≤ gelfandRadius T := by
    intro t f hf hTf
    by_contra h
    have hu := spectrum.mem_resolventSet_iff.1
      (mem_resolventSet_of_gelfandRadius_lt (a := T) (k := t) (by
        rw [Real.norm_eq_abs]
        exact not_le.1 h))
    exact hf (ContinuousLinearMap.eq_zero_of_isUnit_of_apply_eq_zero hu (by
      simp [Algebra.algebraMap_eq_smul_one, hTf]))
  have hcs : ∀ (c : ℝ) (v : Lp ℂ 2 μ), (c : ℂ) • v = c • v := fun c v ↦ by
    rw [← smul_one_smul ℂ c v, Complex.real_smul, mul_one]
  have hev : ∀ (t : ℝ) (v : Lp ℂ 2 μ), Q v = (t : ℂ) • v →
      T (Complex.reCLM.compLpL 2 μ v) = t • Complex.reCLM.compLpL 2 μ v ∧
        T (Complex.imCLM.compLpL 2 μ v) = t • Complex.imCLM.compLpL 2 μ v := fun t v hv ↦
    ⟨by rw [hT, ← Lp.reCLM_compLpL_apply_eq_of_real_kernel hQ v, hv, hcs, map_smul],
      by rw [hT, ← Lp.imCLM_compLpL_apply_eq_of_real_kernel hQ v, hv, hcs, map_smul]⟩
  have hspan := ContinuousLinearMap.maxGenEigenspace_eq_span_of_gelfandRadius_sub_lt hTx₀ hℓT
    hℓx₀ hgap
  have hsT : ∀ f : Lp ℝ 2 μ, T f = gelfandRadius T • f → ∃ c : ℝ, c • x₀ = f := fun f hf ↦ by
    have hm : f ∈ Module.End.maxGenEigenspace (T : Module.End ℝ (Lp ℝ 2 μ)) (gelfandRadius T) :=
      Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hf)
    rw [hspan] at hm
    exact Submodule.mem_span_singleton.1 hm
  have hι0 : Complex.ofRealCLM.compLpL 2 μ x₀ ≠ 0 := fun h ↦ by
    have h' := Lp.reCLM_compLpL_ofRealCLM_compLpL x₀
    rw [h, map_zero] at h'
    rw [← h', map_zero] at hℓx₀
    exact zero_ne_one hℓx₀
  have hQx₀ : Q (Complex.ofRealCLM.compLpL 2 μ x₀) =
      (gelfandRadius T : ℂ) • Complex.ofRealCLM.compLpL 2 μ x₀ := by
    rw [← Lp.ofRealCLM_compLpL_reCLM_compLpL_apply_ofRealCLM_compLpL hQ x₀, ← hT x₀, hTx₀,
      map_smul, hcs]
  have hspanQ : ∀ w : Lp ℂ 2 μ, Q w = (gelfandRadius T : ℂ) • w →
      ∃ c : ℂ, c • Complex.ofRealCLM.compLpL 2 μ x₀ = w := by
    intro w hw
    obtain ⟨a', ha'⟩ := hsT _ (hev _ w hw).1
    obtain ⟨b', hb'⟩ := hsT _ (hev _ w hw).2
    refine ⟨(a' : ℂ) + (b' : ℂ) * Complex.I, ?_⟩
    conv_rhs => rw [← Lp.ofRealCLM_compLpL_reCLM_compLpL_add_I_smul w]
    rw [← ha', ← hb', map_smul, map_smul, add_smul, mul_smul, hcs, hcs, smul_comm b' Complex.I]
  refine ⟨hr, ⟨x₀, ⟨a, ha, hax₀⟩, hι0, hQx₀⟩, fun Ω hΩ0 hQΩ v hv ↦ ?_, fun t v hv0 hv ↦ ?_⟩
  · obtain ⟨c, hc⟩ := hspanQ Ω hQΩ
    obtain ⟨d, hd⟩ := hspanQ v hv
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hΩ0 hc.symm
    refine Submodule.mem_span_singleton.2 ⟨d * c⁻¹, ?_⟩
    rw [← hc, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one, hd]
  · by_cases hre : Complex.reCLM.compLpL 2 μ v = 0
    · refine hbd t (Complex.imCLM.compLpL 2 μ v) (fun him ↦ hv0 ?_) (hev t v hv).2
      rw [← Lp.ofRealCLM_compLpL_reCLM_compLpL_add_I_smul v, hre, him, map_zero, smul_zero,
        add_zero]
    · exact hbd t _ hre (hev t v hv).1

end JentzschComplex
