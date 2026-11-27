/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import MCMC.ToMathlib.Probability.Kernel.Invariance

/-!
# Reversibility does not determine `π ⊗ₘ κ` without σ-finiteness

`ProbabilityTheory.Kernel.isReversible_iff_map_swap_compProd` (in
`MCMC/ToMathlib/Probability/Kernel/Invariance.lean`) identifies reversibility with the invariance
of `π ⊗ₘ κ` under `Prod.swap` when the first marginal `(π ⊗ₘ κ).fst` is σ-finite. The
counterexamples below show that this hypothesis cannot be dropped, whether it fails through `π`
(an infinite multiple of a probability measure) or through `κ` (a kernel of infinite mass). They
rest on one probability measure on `ℝ`, the Gaussian `N(0, 1)`, with a Markov kernel for which
`ν ⊗ₘ κ` and its swap have the same null rectangles but are not mutually absolutely continuous.

## Main statements

* `exists_compProd_prod_eq_zero_iff_and_not_absolutelyContinuous`.
* `exists_isReversible_smul_top_and_map_swap_compProd_ne`,
  `exists_isReversible_withDensity_top_and_map_swap_compProd_ne`.

Staged for Mathlib's `Counterexamples/` (new file): the Gaussian measure is the only reason for the
import of `Mathlib.Probability.Distributions.Gaussian.Real`, which
`Mathlib/Probability/Kernel/Invariance.lean` should not import.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {X : Type*} {mX : MeasurableSpace X} {κ : Kernel X X} {π : Measure X}

/-- With `ν = N(0, 1)` on `ℝ` and the Markov kernel `κ x = (N(0, 1) + δ_{x + 1}) / 2`, the
measure `ν ⊗ₘ κ` and its image under the swap have the same null rectangles, but the graph
`{p | p.2 - 1 = p.1}` is null for the image and not for `ν ⊗ₘ κ`. -/
theorem exists_compProd_prod_eq_zero_iff_and_not_absolutelyContinuous :
    ∃ (ν : Measure ℝ) (κ : Kernel ℝ ℝ), IsProbabilityMeasure ν ∧ IsMarkovKernel κ ∧
      (∀ ⦃s t : Set ℝ⦄, MeasurableSet s → MeasurableSet t →
        ((ν ⊗ₘ κ) (s ×ˢ t) = 0 ↔ (ν ⊗ₘ κ) (t ×ˢ s) = 0)) ∧
      ¬ ν ⊗ₘ κ ≪ (ν ⊗ₘ κ).map Prod.swap := by
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  set γ := gaussianReal 0 1
  set κ₀ : Kernel ℝ ℝ := Kernel.const ℝ γ + Kernel.deterministic (· + 1) (measurable_add_const 1)
  have hκ₀ : γ ⊗ₘ κ₀.withDensity (fun _ _ ↦ 2⁻¹) =
      (2⁻¹ : ℝ≥0∞) • (γ.prod γ + γ.map fun x ↦ (x, x + 1)) := by
    rw [Measure.compProd_withDensity measurable_const, withDensity_const,
      Measure.compProd_add_right, Measure.compProd_const, Measure.compProd_deterministic]
  have hM : IsMarkovKernel (κ₀.withDensity fun _ _ ↦ 2⁻¹) := ⟨fun x ↦ ⟨by
    rw [Kernel.withDensity_apply _ measurable_const, withDensity_const, Measure.smul_apply,
      add_apply, Measure.add_apply, const_apply, deterministic_apply, measure_univ,
      measure_univ, smul_eq_mul, one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero
      ENNReal.ofNat_ne_top]⟩⟩
  have hgm : Measurable fun x : ℝ ↦ (x, x + 1) := measurable_id'.prodMk (measurable_add_const 1)
  have htr : ∀ t, γ t = 0 → γ ((· + 1) ⁻¹' t) = 0 := fun t ht ↦
    gaussianReal_absolutelyContinuous 0 one_ne_zero (by
      rw [measure_preimage_add_right]; exact gaussianReal_absolutelyContinuous' 0 one_ne_zero ht)
  have hrect : ∀ ⦃s t : Set ℝ⦄, MeasurableSet s → MeasurableSet t →
      ((γ.prod γ + γ.map fun x ↦ (x, x + 1) : Measure (ℝ × ℝ)) (s ×ˢ t) = 0 ↔
        γ s = 0 ∨ γ t = 0) := by
    intro s t hs ht
    rw [Measure.add_apply, Measure.prod_prod,
      Measure.map_apply hgm (hs.prod ht),
      mk_preimage_prod, preimage_id', add_eq_zero, mul_eq_zero]
    refine ⟨And.left, fun h ↦ ⟨h, h.elim (measure_mono_null inter_subset_left)
      fun h' ↦ measure_mono_null inter_subset_right (htr t h')⟩⟩
  have hG : MeasurableSet {p : ℝ × ℝ | p.2 - 1 = p.1} :=
    measurableSet_eq_fun (measurable_snd.sub_const 1) measurable_fst
  refine ⟨γ, _, inferInstance, hM, fun s t hs ht ↦ ?_, fun hac ↦ ?_⟩
  · rw [hκ₀, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, mul_eq_zero,
      mul_eq_zero, hrect hs ht, hrect ht hs]
    exact or_congr_right or_comm
  have h0 := @hac {p : ℝ × ℝ | p.2 - 1 = p.1} (by
    rw [hκ₀, Measure.map_smul _ measurable_swap.aemeasurable, Measure.smul_apply,
      Measure.map_apply measurable_swap hG, Measure.add_apply,
      Measure.prod_apply (measurable_swap hG), Measure.map_apply hgm (measurable_swap hG)]
    simp [show ∀ a : ℝ, a - 1 ≠ a + 1 from fun a h ↦ by linarith])
  rw [hκ₀, Measure.smul_apply, Measure.add_apply, Measure.map_apply hgm hG] at h0
  simp at h0

/-- σ-finiteness of the first marginal is needed in `isReversible_iff_map_swap_compProd`, even
for a Markov kernel: a Markov kernel on `ℝ` is reversible for the s-finite measure `∞ • ν` with
`ν` a probability measure (the first marginal is `∞ • ν`), and `(∞ • ν) ⊗ₘ κ` is not invariant
under the swap. -/
theorem exists_isReversible_smul_top_and_map_swap_compProd_ne :
    ∃ (ν : Measure ℝ) (κ : Kernel ℝ ℝ), IsProbabilityMeasure ν ∧ IsMarkovKernel κ ∧
      κ.IsReversible (∞ • ν) ∧ ((∞ • ν) ⊗ₘ κ).map Prod.swap ≠ (∞ • ν) ⊗ₘ κ := by
  obtain ⟨ν, κ, hν, hκ, hnull, hac⟩ := exists_compProd_prod_eq_zero_iff_and_not_absolutelyContinuous
  refine ⟨ν, κ, hν, hκ, fun s t hs ht ↦ ?_, fun h ↦ hac fun s hs ↦ ?_⟩
  · rw [← Measure.compProd_apply_prod hs ht, ← Measure.compProd_apply_prod ht hs,
      Measure.compProd_smul_left, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul]
    by_cases h0 : (ν ⊗ₘ κ) (s ×ˢ t) = 0
    · rw [h0, (hnull hs ht).1 h0]
    · rw [ENNReal.top_mul h0, ENNReal.top_mul (mt (hnull hs ht).2 h0)]
  · rw [Measure.compProd_smul_left, Measure.map_smul _ measurable_swap.aemeasurable] at h
    have h's := congrArg (· s) h
    simp only [Measure.smul_apply, smul_eq_mul, hs, mul_zero] at h's
    exact (mul_eq_zero.1 h's.symm).resolve_left ENNReal.top_ne_zero

/-- σ-finiteness of the first marginal is needed in `isReversible_iff_map_swap_compProd` for a
probability measure `π`: for a Markov kernel `Q` on `ℝ`, the kernel `Q.withDensity fun _ _ ↦ ∞`,
of infinite mass at every point (the first marginal is `∞ • π`), is `π`-reversible and its
composition-product with `π` is not invariant under the swap. -/
theorem exists_isReversible_withDensity_top_and_map_swap_compProd_ne :
    ∃ (π : Measure ℝ) (Q : Kernel ℝ ℝ) (_ : IsMarkovKernel Q), IsProbabilityMeasure π ∧
      (Q.withDensity fun _ _ ↦ ∞).IsReversible π ∧
      (π ⊗ₘ Q.withDensity fun _ _ ↦ ∞).map Prod.swap ≠ π ⊗ₘ Q.withDensity fun _ _ ↦ ∞ := by
  obtain ⟨ν, κ, hν, hκ, hrev, hne⟩ := exists_isReversible_smul_top_and_map_swap_compProd_ne
  have heq : ν ⊗ₘ κ.withDensity (fun _ _ ↦ ∞) = (∞ • ν) ⊗ₘ κ := by
    rw [Measure.compProd_withDensity measurable_const, withDensity_const,
      Measure.compProd_smul_left]
  refine ⟨ν, κ, hκ, hν, fun s t hs ht ↦ ?_, by rw [heq]; exact hne⟩
  rw [← Measure.compProd_apply_prod hs ht, ← Measure.compProd_apply_prod ht hs, heq,
    Measure.compProd_apply_prod hs ht, Measure.compProd_apply_prod ht hs, hrev hs ht]

end ProbabilityTheory.Kernel
