/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.WithDensity

/-!
# A kernel with any density with respect to an s-finite kernel is s-finite

Mathlib proves `IsSFiniteKernel (κ.withDensity f)` for an s-finite `κ` when `f` takes no infinite
value (`ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity`). The restriction is not needed:
`f` is the sum of `f` off `{f = ∞}` and countably many copies of the indicator of `{f = ∞}`, each
a finite density. This is the kernel version of `MeasureTheory.Measure.withDensity.instSFinite`.

Staged for `Mathlib/Probability/Kernel/WithDensity.lean`. Searched on 2026-11-26 in the pinned
Mathlib: `grep -rn "IsSFiniteKernel (withDensity\|IsSFiniteKernel (κ.withDensity"
Mathlib/Probability` finds the instance for `ℝ≥0`-valued densities and the theorem with
`∀ a b, f a b ≠ ∞`, nothing for arbitrary densities.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- A kernel with an arbitrary density with respect to an s-finite kernel is s-finite. -/
instance isSFiniteKernel_withDensity (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → β → ℝ≥0∞) :
    IsSFiniteKernel (κ.withDensity f) := by
  by_cases hf : Measurable (Function.uncurry f)
  swap
  · rw [withDensity_of_not_measurable _ hf]
    infer_instance
  have hs : MeasurableSet {p : α × β | Function.uncurry f p = ∞} := hf (measurableSet_singleton _)
  set g : α → β → ℝ≥0∞ := fun a b ↦ {p | Function.uncurry f p = ∞}ᶜ.indicator
    (Function.uncurry f) (a, b) with hg_def
  set h : α → β → ℝ≥0∞ := fun a b ↦ {p | Function.uncurry f p = ∞}.indicator 1 (a, b)
    with hh_def
  have hg : Measurable (Function.uncurry g) := hf.indicator hs.compl
  have hh : Measurable (Function.uncurry h) := measurable_one.indicator hs
  have hfgh : ∀ a b, f a b = g a b + ∑' _ : ℕ, h a b := fun a b ↦ by
    by_cases hab : f a b = ∞ <;> simp [hg_def, hh_def, hab]
  have heq : κ.withDensity f = κ.withDensity g + Kernel.sum fun _ : ℕ ↦ κ.withDensity h := by
    ext a s hs
    rw [add_apply, Measure.add_apply, sum_apply' _ _ hs,
      Kernel.withDensity_apply' _ hf, Kernel.withDensity_apply' _ hg]
    simp_rw [Kernel.withDensity_apply' _ hh, hfgh a]
    rw [lintegral_add_left hg.of_uncurry_left,
      lintegral_tsum fun _ ↦ hh.of_uncurry_left.aemeasurable]
  have : IsSFiniteKernel (κ.withDensity g) := IsSFiniteKernel.withDensity κ fun a b ↦ by
    by_cases hab : f a b = ∞ <;> simp [hg_def, hab]
  have : IsSFiniteKernel (κ.withDensity h) := IsSFiniteKernel.withDensity κ fun a b ↦ by
    by_cases hab : f a b = ∞ <;> simp [hh_def, hab]
  rw [heq]
  infer_instance

end ProbabilityTheory.Kernel
