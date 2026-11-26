/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# The first marginal of `μ ⊗ₘ κ`, σ-finiteness, and random maps

The first marginal of `μ ⊗ₘ κ` is `μ` with density `a ↦ κ a univ` (for a Markov kernel it is `μ`,
Mathlib's `MeasureTheory.Measure.fst_compProd`). Hence `μ ⊗ₘ κ` and its first marginal are
σ-finite when `μ` is σ-finite and `κ a` is a finite measure for `μ`-almost every `a`; in particular
for every finite kernel. For the kernel `(Kernel.id ×ₖ Kernel.const α ν).map F` of the random map
`x ↦ F (x, w)`, `w ∼ ν`, the measure `μ ⊗ₘ _` is the image of `μ.prod ν` under `p ↦ (p.1, F p)`.

Staged for `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean`. Searched on 2026-11-26 in
the pinned Mathlib: `grep -rn "SigmaFinite (μ ⊗ₘ\|SigmaFinite (.* ⊗ₘ" Mathlib` has no hit (the
instances on `μ ⊗ₘ κ` are `SFinite`, `IsFiniteMeasure`, `IsProbabilityMeasure`,
`IsZeroOrProbabilityMeasure`); `Measure.fst_compProd` is stated for Markov kernels only;
`grep -rn "id ×ₖ" Mathlib/Probability/Kernel/Composition` finds no composition-product with the
kernel of a random map; `grep -rn "compProd_apply_singleton\|dirac_compProd_apply"
Mathlib/Probability` finds only `dirac_compProd_apply`, for a Dirac first factor.
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

instance sigmaFinite_compProd_of_isFiniteKernel [SigmaFinite μ]
    [ProbabilityTheory.IsFiniteKernel κ] : SigmaFinite (μ ⊗ₘ κ) :=
  sigmaFinite_compProd (ae_of_all _ fun _ ↦ measure_ne_top _ _)

/-- The mass of `μ ⊗ₘ κ` at a point. -/
lemma compProd_apply_singleton [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [SFinite μ] [ProbabilityTheory.IsSFiniteKernel κ] (a : α) (b : β) :
    (μ ⊗ₘ κ) {(a, b)} = μ {a} * κ a {b} := by
  rw [← singleton_prod_singleton, compProd_apply_prod (measurableSet_singleton a)
    (measurableSet_singleton b), lintegral_singleton, mul_comm]

/-- The composition-product of `μ` with the kernel of the random map `x ↦ F (x, w)`, `w ∼ ν`, is the
image of `μ.prod ν` under `p ↦ (p.1, F p)`. -/
lemma compProd_map_id_prod_const [SFinite μ] {γ : Type*} {mγ : MeasurableSpace γ}
    {ν : Measure γ} [SFinite ν] {F : α × γ → β} (hF : Measurable F) :
    μ ⊗ₘ (ProbabilityTheory.Kernel.id ×ₖ ProbabilityTheory.Kernel.const α ν).map F =
      (μ.prod ν).map fun p ↦ (p.1, F p) := by
  refine ext_of_lintegral _ fun g hg ↦ ?_
  rw [lintegral_compProd hg, lintegral_map hg (measurable_fst.prodMk hF),
    lintegral_prod (fun z ↦ g (z.1, F z)) (hg.comp (measurable_fst.prodMk hF)).aemeasurable]
  refine lintegral_congr fun x ↦ ?_
  rw [ProbabilityTheory.Kernel.map_apply _ hF,
    lintegral_map (f := fun b ↦ g (x, b)) (hg.comp measurable_prodMk_left) hF,
    ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.id_apply,
    ProbabilityTheory.Kernel.const_apply, dirac_prod, lintegral_map (f := fun p ↦ g (x, F p))
      ((hg.comp measurable_prodMk_left).comp hF) measurable_prodMk_left]

end MeasureTheory.Measure
