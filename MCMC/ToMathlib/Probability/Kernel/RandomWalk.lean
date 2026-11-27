/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Group.Prod
public import MCMC.ToMathlib.Probability.Kernel.Reversible

/-!
# Random walks with symmetric increments are reversible for invariant measures

On a commutative group, the random walk `x ↦ law of x + W`, `W ∼ ν`, is `μ`-reversible for every
s-finite translation-invariant measure `μ` (Lebesgue measure on `ℝⁿ`, a Haar measure, the counting
measure on `ℤ`) when the increment law is symmetric, `ν.map Neg.neg = ν`. The measure `μ` need not
be finite; this is the proposal of the random-walk Metropolis algorithm.

Staged for `Mathlib/Probability/Kernel/RandomWalk.lean` (new file). Searched on 2026-11-26 in the
pinned Mathlib: `grep -rn "IsReversible" Mathlib` finds only `Probability/Kernel/Invariance.lean`;
`grep -rln "random walk" Mathlib/Probability` finds no kernel of a random walk.
-/

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

/-- **A random walk with symmetric increments is reversible** for every s-finite
translation-invariant measure. -/
theorem isReversible_map_add_of_map_neg {μ ν : Measure G} [SFinite μ] [SFinite ν]
    [μ.IsAddLeftInvariant] (hν : ν.map Neg.neg = ν) :
    ((Kernel.id ×ₖ Kernel.const G ν).map fun p : G × G ↦ p.1 + p.2).IsReversible μ := by
  have hL : Measurable fun p : G × G ↦ (p.1, p.1 + p.2) := by fun_prop
  have hM : (μ.prod ν).map (Prod.map id Neg.neg ∘ Prod.swap ∘ (fun z : G × G ↦ (z.1, z.1 + z.2)) ∘
      Prod.swap) = μ.prod ν := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop)
        (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop), Measure.prod_swap,
      (measurePreserving_prod_add ν μ).map_eq, Measure.prod_swap,
      ← Measure.map_prod_map _ _ measurable_id measurable_neg, Measure.map_id, hν]
  have hF : Measurable (Function.uncurry fun x w : G ↦ x + w) := measurable_add
  refine IsReversible.of_map_swap_compProd ?_
  rw [Measure.compProd_eq_map_prod (Q := (Kernel.id ×ₖ Kernel.const G ν).map
      fun p : G × G ↦ p.1 + p.2) hF (Kernel.map_prod_const_apply hF ν) μ,
    Measure.map_map measurable_swap hL]
  calc (μ.prod ν).map (Prod.swap ∘ fun p : G × G ↦ (p.1, p.1 + p.2))
      = ((μ.prod ν).map (Prod.map id Neg.neg ∘ Prod.swap ∘ (fun z : G × G ↦ (z.1, z.1 + z.2)) ∘
          Prod.swap)).map fun p : G × G ↦ (p.1, p.1 + p.2) := by
        rw [Measure.map_map hL (by fun_prop)]
        congr 1
        funext p
        simp [add_comm p.2 p.1]
    _ = (μ.prod ν).map fun p : G × G ↦ (p.1, p.1 + p.2) := by rw [hM]

end ProbabilityTheory.Kernel
