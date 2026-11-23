/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import MCMC.ToMathlib.Analysis.Normed.Operator.KreinRutman.Order
public import MCMC.ToMathlib.MeasureTheory.Function.LpOrder

/-!
# Jentzsch's theorem on the real `L²` of a finite measure

Let `μ` be a finite nonzero measure and `T` a compact operator on the real `L²(μ)` with a kernel
bounded between two constants, `0 < c₁ ≤ k ≤ c₂`: `(T f)(x) = ∫ k(x, y) f(y) dμ(y)` for
`μ`-almost every `x`. Then `T` is `u₀`-positive for the constant function `u₀ = 1`, with
`ψ f = c₁ ∫ f`: `ψ f • 1 ≤ T f` for `f ≥ 0`, and `T f ≤ (c₂ ‖1‖ ‖f‖) • 1` by Cauchy–Schwarz
(`∫ |f| = ⟪1, |f|⟫ ≤ ‖1‖ ‖f‖`). The Krein–Rutman theorem for compact `u₀`-positive operators then
gives the positive eigenvector, the positive transpose eigenfunctional and the spectral gap.

## Main statements

* `MeasureTheory.L2.inner_const_one`: `⟪1, f⟫ = ∫ f` in the real `L²` of a finite measure.
* `IsCompactOperator.exists_gelfandRadius_sub_smul_smulRight_lt_of_pos_kernel` (**Jentzsch**):
  `r = gelfandRadius T > 0`, `T x₀ = r • x₀` for some `x₀ ≥ a • 1` with `a > 0`, the transpose has
  an eigenfunctional `ℓ` for `r`, positive on nonzero nonnegative functions, with `ℓ x₀ = 1`, and
  `gelfandRadius (T - r • ℓ.smulRight x₀) < r`.

## References

* R. Jentzsch, *Über Integralgleichungen mit positivem Kern*, J. reine angew. Math. 141 (1912).
* M. A. Krasnosel'skii, *Positive solutions of operator equations*, Noordhoff, 1964, §2.

Staged for `Mathlib/Analysis/Normed/Operator/KreinRutman.lean`. Searched on 2026-11-23: the word
`Jentzsch` occurs nowhere in the pinned Mathlib.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped InnerProductSpace

namespace MeasureTheory.L2

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- In the real `L²` of a finite measure, the inner product with the constant function `1` is the
integral. -/
theorem inner_const_one (f : Lp ℝ 2 μ) : ⟪Lp.const 2 μ (1 : ℝ), f⟫_ℝ = ∫ x, f x ∂μ := by
  rw [← indicatorConstLp_univ, inner_indicatorConstLp_one MeasurableSet.univ,
    Measure.restrict_univ]

end MeasureTheory.L2

section Jentzsch

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ]
  {T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {k : X × X → ℝ} {c₁ c₂ : ℝ}

/-- **Jentzsch's theorem** on the real `L²(μ)` of a finite nonzero measure: let `T` be compact
with `(T f)(x) = ∫ k(x, y) f(y) dμ(y)` for `μ`-almost every `x`, every section `k(x, ·)` almost
everywhere strongly measurable, and `0 < c₁ ≤ k ≤ c₂`. Then `r = gelfandRadius T > 0`,
`T x₀ = r • x₀` for some `x₀ ≥ a • 1` with `a > 0`, the transpose has an eigenfunctional `ℓ` for
`r`, positive on nonzero nonnegative functions, with `ℓ x₀ = 1`, and
`gelfandRadius (T - r • ℓ.smulRight x₀) < r`. -/
theorem IsCompactOperator.exists_gelfandRadius_sub_smul_smulRight_lt_of_pos_kernel
    (hTc : IsCompactOperator T)
    (hk : ∀ f : Lp ℝ 2 μ, (T f : X → ℝ) =ᵐ[μ] fun x ↦ ∫ y, k (x, y) * f y ∂μ)
    (hkm : ∀ x, AEStronglyMeasurable (fun y ↦ k (x, y)) μ) (hc₁ : 0 < c₁)
    (hk₁ : ∀ p, c₁ ≤ k p) (hk₂ : ∀ p, k p ≤ c₂) :
    0 < gelfandRadius T ∧ ∃ x₀ : Lp ℝ 2 μ, 0 ≤ x₀ ∧ ∃ a : ℝ, 0 < a ∧
      a • Lp.const 2 μ (1 : ℝ) ≤ x₀ ∧ ∃ ℓ : StrongDual ℝ (Lp ℝ 2 μ),
      T x₀ = gelfandRadius T • x₀ ∧ ℓ.comp T = gelfandRadius T • ℓ ∧ ℓ x₀ = 1 ∧
      (∀ x, 0 ≤ x → x ≠ 0 → 0 < ℓ x) ∧
      gelfandRadius (T - gelfandRadius T • ℓ.smulRight x₀) < gelfandRadius T := by
  have hE : Dense (Submodule.span ℝ (Ici (0 : Lp ℝ 2 μ)) : Set (Lp ℝ 2 μ)) := by
    rw [Submodule.span_Ici_zero_eq_top, Submodule.top_coe]
    exact dense_univ
  have hu : (0 : Lp ℝ 2 μ) ≤ Lp.const 2 μ (1 : ℝ) := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ))] with x hx
    rw [Pi.zero_apply, hx]
    exact zero_le_one
  have hu0 : Lp.const 2 μ (1 : ℝ) ≠ 0 := by
    rw [← norm_pos_iff, Lp.norm_const (p := 2) (μ := μ) (c := (1 : ℝ)) two_ne_zero, norm_one,
      one_mul]
    exact Real.rpow_pos_of_pos measureReal_univ_pos _
  have hint (f : Lp ℝ 2 μ) : Integrable f μ := (Lp.memLp f).integrable one_le_two
  have hkb (p : X × X) : ‖k p‖ ≤ c₂ := by
    rw [Real.norm_eq_abs, abs_of_pos (hc₁.trans_le (hk₁ p))]
    exact hk₂ p
  have hsec (f : Lp ℝ 2 μ) (x : X) : Integrable (fun y ↦ k (x, y) * f y) μ :=
    (hint f).bdd_mul (hkm x) (ae_of_all _ fun y ↦ hkb (x, y))
  have hpos (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (hf0 : f ≠ 0) : 0 < ∫ x, f x ∂μ := by
    have hf' := (Lp.coeFn_nonneg f).2 hf
    refine (integral_nonneg_of_ae hf').lt_of_ne fun h ↦ hf0 ?_
    exact Lp.eq_zero_iff_ae_eq_zero.2 ((integral_eq_zero_iff_of_nonneg_ae hf' (hint f)).1 h.symm)
  have hψ (f : Lp ℝ 2 μ) :
      (c₁ • innerSL ℝ (Lp.const 2 μ (1 : ℝ))) f = c₁ * ∫ x, f x ∂μ := by
    rw [smul_apply, innerSL_apply_apply, L2.inner_const_one, smul_eq_mul]
  have hψpos (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (hf0 : f ≠ 0) :
      0 < (c₁ • innerSL ℝ (Lp.const 2 μ (1 : ℝ))) f := by
    rw [hψ]
    exact mul_pos hc₁ (hpos f hf hf0)
  have hlow (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
      (c₁ • innerSL ℝ (Lp.const 2 μ (1 : ℝ))) f • Lp.const 2 μ (1 : ℝ) ≤ T f := by
    have hf' := (Lp.coeFn_nonneg f).2 hf
    rw [hψ, ← Lp.coeFn_le]
    filter_upwards [Lp.coeFn_smul (c₁ * ∫ x, f x ∂μ) (Lp.const 2 μ (1 : ℝ)),
      Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ)), hk f] with x h₁ h₂ h₃
    rw [h₁, Pi.smul_apply, h₂, h₃, Function.const_apply, smul_eq_mul, mul_one,
      ← integral_const_mul]
    exact integral_mono_ae ((hint f).const_mul c₁) (hsec f x)
      (hf'.mono fun y hy ↦ mul_le_mul_of_nonneg_right (hk₁ (x, y)) hy)
  have hup (f : Lp ℝ 2 μ) :
      T f ≤ ((c₂ * ‖Lp.const 2 μ (1 : ℝ)‖) * ‖f‖) • Lp.const 2 μ (1 : ℝ) := by
    have hab : ∫ x, |f x| ∂μ ≤ ‖Lp.const 2 μ (1 : ℝ)‖ * ‖f‖ := by
      have h := real_inner_le_norm (Lp.const 2 μ (1 : ℝ)) |f|
      rwa [L2.inner_const_one, norm_abs_eq_norm, integral_congr_ae (Lp.coeFn_abs f)] at h
    rw [← Lp.coeFn_le]
    filter_upwards [Lp.coeFn_smul ((c₂ * ‖Lp.const 2 μ (1 : ℝ)‖) * ‖f‖) (Lp.const 2 μ (1 : ℝ)),
      Lp.coeFn_const (p := 2) (μ := μ) (c := (1 : ℝ)), hk f] with x h₁ h₂ h₃
    rw [h₁, Pi.smul_apply, h₂, h₃, Function.const_apply, smul_eq_mul, mul_one, mul_assoc]
    have hc₂ : 0 ≤ c₂ := (norm_nonneg _).trans (hkb (x, x))
    refine (integral_mono_ae (hsec f x) ((hint f).abs.const_mul c₂)
      (ae_of_all _ fun y ↦ ?_)).trans ?_
    · calc k (x, y) * f y ≤ |k (x, y) * f y| := le_abs_self _
        _ = |k (x, y)| * |f y| := abs_mul _ _
        _ ≤ c₂ * |f y| := mul_le_mul_of_nonneg_right
            ((Real.norm_eq_abs _).symm.trans_le (hkb (x, y))) (abs_nonneg _)
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hab hc₂
  exact hTc.exists_gelfandRadius_sub_smul_smulRight_lt_of_smul_le_apply_le hE hu hu0 hψpos hlow hup

end Jentzsch
