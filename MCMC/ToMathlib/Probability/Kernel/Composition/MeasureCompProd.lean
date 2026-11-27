/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# The first marginal of `μ ⊗ₘ κ`, σ-finiteness, and the joint law of a random map

The first marginal of `μ ⊗ₘ κ` is `μ` with density `a ↦ κ a univ` (for a Markov kernel it is `μ`,
Mathlib's `MeasureTheory.Measure.fst_compProd`). Hence `μ ⊗ₘ κ` and its first marginal are
σ-finite when `μ` is σ-finite and `κ a` is a finite measure for `μ`-almost every `a`; in particular
for every finite kernel. The kernel of the random map `x ↦ F x w`, `w ∼ ρ`, is Mathlib's
`(Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F)`, whose value at `x` is `ρ.map (F x)`
(`ProbabilityTheory.Kernel.map_prod_const_apply`); for every kernel with `Q y = ρ.map (F y)`, the
joint law is `μ ⊗ₘ Q = (μ.prod ρ).map (fun p ↦ (p.1, F p.1 p.2))`
(`MeasureTheory.Measure.compProd_eq_map_prod`).

Staged for `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean`. Searched on 2026-11-26 in
the pinned Mathlib: `grep -rn "SigmaFinite (μ ⊗ₘ\|SigmaFinite (.* ⊗ₘ" Mathlib` has no hit (the
instances on `μ ⊗ₘ κ` are `SFinite`, `IsFiniteMeasure`, `IsProbabilityMeasure`,
`IsZeroOrProbabilityMeasure`); `Measure.fst_compProd` is stated for Markov kernels only;
`grep -rn "id ×ₖ" Mathlib/Probability/Kernel/Composition` finds no composition-product with the
kernel of a random map (the nearest is `Measure.compProd_map` of `Composition/Lemmas.lean`,
`μ ⊗ₘ κ.map f = (μ ⊗ₘ κ).map (Prod.map id f)`);
`grep -rn "compProd_apply_singleton\|dirac_compProd_apply" Mathlib/Probability` finds only
`dirac_compProd_apply`, for a Dirac first factor.
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

/-- The joint law of `y ∼ μ` and `F y w` for an independent `w ∼ ρ`: if `Q y = ρ.map (F y)`, then
`μ ⊗ₘ Q = (μ.prod ρ).map (fun p ↦ (p.1, F p.1 p.2))`. -/
theorem compProd_eq_map_prod {X W Y : Type*} {mX : MeasurableSpace X} {mW : MeasurableSpace W}
    {mY : MeasurableSpace Y} {Q : ProbabilityTheory.Kernel Y X}
    [ProbabilityTheory.IsSFiniteKernel Q] {F : Y → W → X} (hF : Measurable (Function.uncurry F))
    {ρ : Measure W} [SFinite ρ] (hQ : ∀ y, Q y = ρ.map (F y)) (μ : Measure Y) [SFinite μ] :
    μ ⊗ₘ Q = (μ.prod ρ).map (fun p ↦ (p.1, F p.1 p.2)) := by
  have hG : Measurable fun p : Y × W ↦ (p.1, F p.1 p.2) := measurable_fst.prodMk hF
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hG hs, Measure.prod_apply (hG hs)]
  refine lintegral_congr fun y ↦ ?_
  rw [hQ, Measure.map_apply hF.of_uncurry_left (measurable_prodMk_left hs)]
  rfl

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

open MeasureTheory

variable {X W Y : Type*} {mX : MeasurableSpace X} {mW : MeasurableSpace W} {mY : MeasurableSpace Y}

/-- The kernel of the random map `x ↦ F x w`, `w ∼ ρ`, at `x` is `ρ.map (F x)`. -/
theorem map_prod_const_apply {F : X → W → Y} (hF : Measurable (Function.uncurry F))
    (ρ : Measure W) [SFinite ρ] (x : X) :
    ((Kernel.id ×ₖ Kernel.const X ρ).map (Function.uncurry F)) x = ρ.map (F x) := by
  rw [Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
  rfl

end ProbabilityTheory.Kernel
