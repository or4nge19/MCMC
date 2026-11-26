/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# The first marginal of `μ ⊗ₘ κ` and σ-finiteness

The first marginal of `μ ⊗ₘ κ` is `μ` with density `a ↦ κ a univ` (for a Markov kernel it is `μ`,
Mathlib's `MeasureTheory.Measure.fst_compProd`). Hence `μ ⊗ₘ κ` and its first marginal are
σ-finite when `μ` is σ-finite and `κ a` is a finite measure for `μ`-almost every `a`; in particular
for every finite kernel.

Staged for `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean`. Searched on 2026-11-26 in
the pinned Mathlib: `grep -rn "SigmaFinite (μ ⊗ₘ\|SigmaFinite (.* ⊗ₘ" Mathlib` has no hit (the
instances on `μ ⊗ₘ κ` are `SFinite`, `IsFiniteMeasure`, `IsProbabilityMeasure`,
`IsZeroOrProbabilityMeasure`); `fst_compProd` is stated for Markov kernels only.
-/

@[expose] public section

open Set
open scoped ENNReal ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {κ : ProbabilityTheory.Kernel α β}

/-- The first marginal of `μ ⊗ₘ κ` is `μ` with density the total mass of `κ`. -/
lemma fst_compProd_eq_withDensity [SFinite μ] [ProbabilityTheory.IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).fst = μ.withDensity fun a ↦ κ a univ := by
  ext s hs
  rw [fst_apply hs, ← prod_univ, compProd_apply_prod hs .univ, withDensity_apply _ hs]

/-- The first marginal of `μ ⊗ₘ κ` is σ-finite if `μ` is and `κ a` is finite for `μ`-almost
every `a`. -/
lemma sigmaFinite_fst_compProd [SigmaFinite μ] [ProbabilityTheory.IsSFiniteKernel κ]
    (h : ∀ᵐ a ∂μ, κ a univ ≠ ∞) : SigmaFinite (μ ⊗ₘ κ).fst := by
  rw [fst_compProd_eq_withDensity]
  exact SigmaFinite.withDensity_of_ne_top h

/-- `μ ⊗ₘ κ` is σ-finite if `μ` is and `κ a` is finite for `μ`-almost every `a`. -/
lemma sigmaFinite_compProd [SigmaFinite μ] [ProbabilityTheory.IsSFiniteKernel κ]
    (h : ∀ᵐ a ∂μ, κ a univ ≠ ∞) : SigmaFinite (μ ⊗ₘ κ) :=
  SigmaFinite.of_map _ measurable_fst.aemeasurable (sigmaFinite_fst_compProd h)

instance [SigmaFinite μ] [ProbabilityTheory.IsFiniteKernel κ] : SigmaFinite (μ ⊗ₘ κ) :=
  sigmaFinite_compProd (ae_of_all _ fun _ ↦ measure_ne_top _ _)

end MeasureTheory.Measure
