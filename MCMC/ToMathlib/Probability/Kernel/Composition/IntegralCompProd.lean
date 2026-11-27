/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The Bochner integral against the composition of a kernel and a measure

`MeasureTheory.Measure.integral_comp`: `∫ f ∂(κ ∘ₘ μ) = ∫ x, ∫ f ∂(κ x) ∂μ`, the Bochner
counterpart of Mathlib's `MeasureTheory.Measure.lintegral_bind`, named after its neighbour
`MeasureTheory.Measure.integrable_comp_iff`.

Searched on 2026-11-25 (Mathlib `d13f23b`): `grep -rn "theorem integral_bind\|lemma integral_bind\|
∂(κ ∘ₘ μ)" MeasureTheory Probability` finds no Bochner statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- The Bochner integral against the composition `κ ∘ₘ μ` of a kernel and a measure. -/
theorem MeasureTheory.Measure.integral_comp (κ : Kernel α β) [IsSFiniteKernel κ] (μ : Measure α)
    [SFinite μ] {f : β → E} (hf : Integrable f (κ ∘ₘ μ)) :
    ∫ y, f y ∂(κ ∘ₘ μ) = ∫ x, ∫ y, f y ∂(κ x) ∂μ := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]
