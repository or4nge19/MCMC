/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Count
public import MCMC.ToMathlib.Probability.Kernel.Invariance

/-!
# Random walks with symmetric increments are reversible for invariant measures

On a group, the random walk `x ↦ law of x * W`, `W ∼ ν`, is `μ`-reversible for every s-finite
right-invariant measure `μ` (Lebesgue measure on `ℝⁿ`, a Haar measure on a unimodular group, the
counting measure on `ℤ`) when the increment law is symmetric, `ν.map Inv.inv = ν`; the additive
statement is `ProbabilityTheory.Kernel.isReversible_map_add_of_map_neg`. The measure `μ` need not
be finite; this is the proposal of the random-walk Metropolis algorithm. Both hypotheses are
needed (`not_isReversible_map_add_dirac_one`, `not_isReversible_map_add_dirac_zero`).

Staged for `Mathlib/Probability/Kernel/RandomWalk.lean` (new file). Searched on 2026-11-26 in the
pinned Mathlib: `grep -rn "IsReversible" Mathlib` finds only `Probability/Kernel/Invariance.lean`;
`grep -rln "random walk" Mathlib/Probability` finds no kernel of a random walk.
-/

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel

/-- **A random walk with symmetric increments is reversible** for every s-finite right-invariant
measure: the kernel `x ↦ law of x * W`, `W ∼ ν` with `ν.map Inv.inv = ν`, is `μ`-reversible. -/
@[to_additive /-- **A random walk with symmetric increments is reversible** for every s-finite
right-invariant measure: the kernel `x ↦ law of x + W`, `W ∼ ν` with `ν.map Neg.neg = ν`, is
`μ`-reversible. -/]
theorem isReversible_map_mul_of_map_inv {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] {μ ν : Measure G} [SFinite μ] [SFinite ν]
    [μ.IsMulRightInvariant] (hν : ν.map Inv.inv = ν) :
    ((Kernel.id ×ₖ Kernel.const G ν).map fun p : G × G ↦ p.1 * p.2).IsReversible μ := by
  have hF : Measurable (Function.uncurry fun x w : G ↦ x * w) := measurable_mul
  have hL : Measurable fun p : G × G ↦ (p.1, p.1 * p.2) := by fun_prop
  have hM : (μ.prod ν).map (Prod.map id Inv.inv ∘ fun z : G × G ↦ (z.1 * z.2, z.2)) =
      μ.prod ν := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), (measurePreserving_mul_prod μ ν).map_eq,
      ← Measure.map_prod_map _ _ measurable_id measurable_inv, Measure.map_id, hν]
  refine IsReversible.of_map_swap_compProd ?_
  rw [Measure.compProd_eq_map_prod (Q := (Kernel.id ×ₖ Kernel.const G ν).map
      fun p : G × G ↦ p.1 * p.2) hF (Kernel.map_prod_const_apply hF ν) μ,
    Measure.map_map measurable_swap hL]
  calc (μ.prod ν).map (Prod.swap ∘ fun p : G × G ↦ (p.1, p.1 * p.2))
      = ((μ.prod ν).map (Prod.map id Inv.inv ∘ fun z : G × G ↦ (z.1 * z.2, z.2))).map
          fun p : G × G ↦ (p.1, p.1 * p.2) := by
        rw [Measure.map_map hL (by fun_prop)]
        congr 1
        funext p
        simp
    _ = (μ.prod ν).map fun p : G × G ↦ (p.1, p.1 * p.2) := by rw [hM]

/-- Symmetry of the increments is needed in `isReversible_map_add_of_map_neg`: the walk
`x ↦ x + 1` on `ℤ` is not reversible for the counting measure. -/
theorem not_isReversible_map_add_dirac_one :
    ¬ ((Kernel.id ×ₖ Kernel.const ℤ (Measure.dirac (1 : ℤ))).map
      fun p : ℤ × ℤ ↦ p.1 + p.2).IsReversible Measure.count := by
  intro h
  have hF : Measurable fun p : ℤ × ℤ ↦ p.1 + p.2 := measurable_of_countable _
  have hK : ∀ y : ℤ, ((Kernel.id ×ₖ Kernel.const ℤ (Measure.dirac (1 : ℤ))).map
      fun p : ℤ × ℤ ↦ p.1 + p.2) y = Measure.dirac (y + 1) := by
    intro y
    rw [Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
      Measure.dirac_prod_dirac, Measure.map_dirac' hF]
  have h1 := h (measurableSet_singleton (0 : ℤ)) (measurableSet_singleton (1 : ℤ))
  simp only [hK] at h1
  rw [Measure.restrict_singleton, Measure.restrict_singleton] at h1
  simp at h1

/-- Invariance of the reference measure is needed in `isReversible_map_add_of_map_neg`: the
symmetric walk `x ↦ x ± 1` on `ℤ` is not reversible for `δ_0`. -/
theorem not_isReversible_map_add_dirac_zero :
    ¬ ((Kernel.id ×ₖ Kernel.const ℤ (Measure.dirac (1 : ℤ) + Measure.dirac (-1))).map
      fun p : ℤ × ℤ ↦ p.1 + p.2).IsReversible (Measure.dirac (0 : ℤ)) := by
  intro h
  have hF : Measurable fun p : ℤ × ℤ ↦ p.1 + p.2 := measurable_of_countable _
  have hK : ∀ y : ℤ, ((Kernel.id ×ₖ Kernel.const ℤ (Measure.dirac (1 : ℤ) +
      Measure.dirac (-1))).map fun p : ℤ × ℤ ↦ p.1 + p.2) y =
        Measure.dirac (y + 1) + Measure.dirac (y + -1) := by
    intro y
    rw [Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
      Measure.prod_add, Measure.dirac_prod_dirac, Measure.dirac_prod_dirac,
      Measure.map_add _ _ hF, Measure.map_dirac' hF, Measure.map_dirac' hF]
  have h1 := h (measurableSet_singleton (0 : ℤ)) (measurableSet_singleton (1 : ℤ))
  simp only [hK] at h1
  rw [Measure.restrict_singleton, Measure.restrict_singleton] at h1
  simp at h1

end ProbabilityTheory.Kernel
